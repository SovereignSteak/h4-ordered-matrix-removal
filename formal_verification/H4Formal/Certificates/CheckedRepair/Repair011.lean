import H4Formal.Certificates.CheckedRepair.Repair010

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_238 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1756 (r0_mode : Int) : ((r0_mode = (0 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int)))))) ↔ ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int))))))) := (iff_congr (normalization_1444 r0_mode) (normalization_1754 r0_mode))

-- Checked replay of trans.
theorem replay_349 (r0_mode : Int) : ((r0_mode = (0 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_238 (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int))))))))
  have n0 : ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ↔ (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_1750 r0_mode) (replay_347 r0_mode)
  have n1 : ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1755 r0_mode) (replay_348 r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1756 r0_mode) hn

theorem normalized_239 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1757 (r0_group : Int) : (r0_group ≤ (1 : Int)) ↔ ((r0_group) ≤ (1 : Int)) := by
  omega

theorem normalization_1758 (r0_group : Int) : (r0_group ≥ (1 : Int)) ↔ (¬ ((r0_group) ≤ (0 : Int))) := by
  omega

theorem normalization_1759 (r0_group : Int) : ((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int))) ↔ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) := (and_congr (normalization_1757 r0_group) (normalization_1758 r0_group))

theorem normalization_1760 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ ((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int)))) ↔ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) := (iff_congr (normalization_1445 r0_group) (normalization_1759 r0_group))

-- Checked replay of rewrite.
theorem replay_350 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ ((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_239 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_1760 r0_group) hn

theorem normalized_240 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1761 (r0_group : Int) : (¬ (r0_group ≤ (1 : Int))) ↔ (¬ ((r0_group) ≤ (1 : Int))) := (not_congr (normalization_1757 r0_group))

theorem normalization_1762 (r0_group : Int) : (¬ (r0_group ≥ (1 : Int))) ↔ (¬ (¬ ((r0_group) ≤ (0 : Int)))) := (not_congr (normalization_1758 r0_group))

theorem normalization_1763 (r0_group : Int) : ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))) ↔ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) := (or_congr (normalization_1761 r0_group) (normalization_1762 r0_group))

theorem normalization_1764 (r0_group : Int) : (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) := (not_congr (normalization_1763 r0_group))

theorem normalization_1765 (r0_group : Int) : (((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int))) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ↔ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := (iff_congr (normalization_1759 r0_group) (normalization_1764 r0_group))

-- Checked replay of rewrite.
theorem replay_351 (r0_group : Int) : (((r0_group ≤ (1 : Int)) ∧ (r0_group ≥ (1 : Int))) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_240 ((r0_group) ≤ (1 : Int)) ((r0_group) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1765 r0_group) hn

theorem normalized_241 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1766 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ↔ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := (iff_congr (normalization_1445 r0_group) (normalization_1764 r0_group))

-- Checked replay of trans.
theorem replay_352 (r0_group : Int) : ((r0_group = (1 : Int)) ↔ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_241 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_1760 r0_group) (replay_350 r0_group)
  have n1 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1765 r0_group) (replay_351 r0_group)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1766 r0_group) hn

theorem normalized_242 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1767 (c1_kind : Int) : (c1_kind ≤ (2 : Int)) ↔ ((c1_kind) ≤ (2 : Int)) := by
  omega

theorem normalization_1768 (c1_kind : Int) : (c1_kind ≥ (2 : Int)) ↔ (¬ ((c1_kind) ≤ (1 : Int))) := by
  omega

theorem normalization_1769 (c1_kind : Int) : ((c1_kind ≤ (2 : Int)) ∧ (c1_kind ≥ (2 : Int))) ↔ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) := (and_congr (normalization_1767 c1_kind) (normalization_1768 c1_kind))

theorem normalization_1770 (c1_kind : Int) : ((c1_kind = (2 : Int)) ↔ ((c1_kind ≤ (2 : Int)) ∧ (c1_kind ≥ (2 : Int)))) ↔ ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) := (iff_congr (normalization_1446 c1_kind) (normalization_1769 c1_kind))

-- Checked replay of rewrite.
theorem replay_353 (c1_kind : Int) : ((c1_kind = (2 : Int)) ↔ ((c1_kind ≤ (2 : Int)) ∧ (c1_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_242 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_1770 c1_kind) hn

theorem normalized_243 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1771 (c1_kind : Int) : (¬ (c1_kind ≤ (2 : Int))) ↔ (¬ ((c1_kind) ≤ (2 : Int))) := (not_congr (normalization_1767 c1_kind))

theorem normalization_1772 (c1_kind : Int) : (¬ (c1_kind ≥ (2 : Int))) ↔ (¬ (¬ ((c1_kind) ≤ (1 : Int)))) := (not_congr (normalization_1768 c1_kind))

theorem normalization_1773 (c1_kind : Int) : ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) := (or_congr (normalization_1771 c1_kind) (normalization_1772 c1_kind))

theorem normalization_1774 (c1_kind : Int) : (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := (not_congr (normalization_1773 c1_kind))

theorem normalization_1775 (c1_kind : Int) : (((c1_kind ≤ (2 : Int)) ∧ (c1_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_1769 c1_kind) (normalization_1774 c1_kind))

-- Checked replay of rewrite.
theorem replay_354 (c1_kind : Int) : (((c1_kind ≤ (2 : Int)) ∧ (c1_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_243 ((c1_kind) ≤ (2 : Int)) ((c1_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1775 c1_kind) hn

theorem normalized_244 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1776 (c1_kind : Int) : ((c1_kind = (2 : Int)) ↔ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_1446 c1_kind) (normalization_1774 c1_kind))

-- Checked replay of trans.
theorem replay_355 (c1_kind : Int) : ((c1_kind = (2 : Int)) ↔ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_244 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
  have n0 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_1770 c1_kind) (replay_353 c1_kind)
  have n1 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1775 c1_kind) (replay_354 c1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1776 c1_kind) hn

theorem normalized_245 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1777 (c1_kind : Int) : (c1_kind ≤ (1 : Int)) ↔ ((c1_kind) ≤ (1 : Int)) := by
  omega

theorem normalization_1778 (c1_kind : Int) : (c1_kind ≥ (1 : Int)) ↔ (¬ ((c1_kind) ≤ (0 : Int))) := by
  omega

theorem normalization_1779 (c1_kind : Int) : ((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int))) ↔ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) := (and_congr (normalization_1777 c1_kind) (normalization_1778 c1_kind))

theorem normalization_1780 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ ((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int)))) ↔ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) := (iff_congr (normalization_1447 c1_kind) (normalization_1779 c1_kind))

-- Checked replay of rewrite.
theorem replay_356 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ ((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_245 (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_1780 c1_kind) hn

theorem normalized_246 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1781 (c1_kind : Int) : (¬ (c1_kind ≤ (1 : Int))) ↔ (¬ ((c1_kind) ≤ (1 : Int))) := (not_congr (normalization_1777 c1_kind))

theorem normalization_1782 (c1_kind : Int) : (¬ (c1_kind ≥ (1 : Int))) ↔ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) := (not_congr (normalization_1778 c1_kind))

theorem normalization_1783 (c1_kind : Int) : ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))) ↔ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))) := (or_congr (normalization_1781 c1_kind) (normalization_1782 c1_kind))

theorem normalization_1784 (c1_kind : Int) : (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) := (not_congr (normalization_1783 c1_kind))

theorem normalization_1785 (c1_kind : Int) : (((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) ↔ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_1779 c1_kind) (normalization_1784 c1_kind))

-- Checked replay of rewrite.
theorem replay_357 (c1_kind : Int) : (((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_246 ((c1_kind) ≤ (1 : Int)) ((c1_kind) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1785 c1_kind) hn

theorem normalized_247 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1786 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) ↔ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_1447 c1_kind) (normalization_1784 c1_kind))

-- Checked replay of trans.
theorem replay_358 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_247 (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))))
  have n0 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_1780 c1_kind) (replay_356 c1_kind)
  have n1 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1785 c1_kind) (replay_357 c1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1786 c1_kind) hn

theorem normalized_248 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1787 (c1_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) := by
  omega

theorem normalization_1788 (c1_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_1789 (c1_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := (and_congr (normalization_1787 c1_depth r0_level) (normalization_1788 c1_depth r0_level))

theorem normalization_1790 (c1_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ↔ (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_1618 c1_depth r0_level) (normalization_1789 c1_depth r0_level))

-- Checked replay of rewrite.
theorem replay_359 (c1_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_248 ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_1790 c1_depth r0_level) hn

abbrev formula_456 (c1_depth r0_level : Int) : Prop := ((((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))))

theorem normalized_249 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1791 (c1_depth r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) := (not_congr (normalization_1787 c1_depth r0_level))

theorem normalization_1792 (c1_depth r0_level : Int) : (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := (not_congr (normalization_1788 c1_depth r0_level))

theorem normalization_1793 (c1_depth r0_level : Int) : ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (or_congr (normalization_1791 c1_depth r0_level) (normalization_1792 c1_depth r0_level))

theorem normalization_1794 (c1_depth r0_level : Int) : (¬ ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) := (not_congr (normalization_1793 c1_depth r0_level))

theorem normalization_1795 (c1_depth r0_level : Int) : (formula_456 c1_depth r0_level) ↔ (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) := (iff_congr (normalization_1789 c1_depth r0_level) (normalization_1794 c1_depth r0_level))

-- Checked replay of rewrite.
theorem replay_360 (c1_depth r0_level : Int) : (formula_456 c1_depth r0_level) := by
  classical
  have ht := (normalized_249 ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1795 c1_depth r0_level) hn

theorem normalized_250 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1796 (c1_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) ↔ (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) := (iff_congr (normalization_1618 c1_depth r0_level) (normalization_1794 c1_depth r0_level))

-- Checked replay of trans.
theorem replay_361 (c1_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_250 ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))))
  have n0 : (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_1790 c1_depth r0_level) (replay_359 c1_depth r0_level)
  have n1 : (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_1795 c1_depth r0_level) (replay_360 c1_depth r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1796 c1_depth r0_level) hn

theorem normalized_251 (p0 p1 p2 p3 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1797 (c1_sign : Int) : (c1_sign ≤ (0 : Int)) ↔ ((c1_sign) ≤ (0 : Int)) := by
  omega

theorem normalization_1798 (c1_sign : Int) : (¬ (c1_sign ≤ (0 : Int))) ↔ (¬ ((c1_sign) ≤ (0 : Int))) := (not_congr (normalization_1797 c1_sign))

theorem normalization_1799 (c1_sign : Int) : (c1_sign ≥ (0 : Int)) ↔ (¬ ((c1_sign) ≤ (-1 : Int))) := by
  omega

theorem normalization_1800 (c1_sign : Int) : (¬ (c1_sign ≥ (0 : Int))) ↔ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) := (not_congr (normalization_1799 c1_sign))

theorem normalization_1801 (c1_sign : Int) : ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))) ↔ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int))))) := (or_congr (normalization_1798 c1_sign) (normalization_1800 c1_sign))

theorem normalization_1802 (c1_sign : Int) : (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ↔ (¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) := (not_congr (normalization_1801 c1_sign))

theorem normalization_1803 (c1_sign : Int) : (c1_sign ≤ (2 : Int)) ↔ ((c1_sign) ≤ (2 : Int)) := by
  omega

theorem normalization_1804 (c1_sign : Int) : (¬ (c1_sign ≤ (2 : Int))) ↔ (¬ ((c1_sign) ≤ (2 : Int))) := (not_congr (normalization_1803 c1_sign))

theorem normalization_1805 (c1_sign : Int) : (c1_sign ≥ (2 : Int)) ↔ (¬ ((c1_sign) ≤ (1 : Int))) := by
  omega

theorem normalization_1806 (c1_sign : Int) : (¬ (c1_sign ≥ (2 : Int))) ↔ (¬ (¬ ((c1_sign) ≤ (1 : Int)))) := (not_congr (normalization_1805 c1_sign))

theorem normalization_1807 (c1_sign : Int) : ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))) ↔ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))) := (or_congr (normalization_1804 c1_sign) (normalization_1806 c1_sign))

theorem normalization_1808 (c1_sign : Int) : (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))) ↔ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))) := (not_congr (normalization_1807 c1_sign))

theorem normalization_1809 (c1_sign : Int) : ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))) := (or_congr (normalization_1802 c1_sign) (normalization_1808 c1_sign))

theorem normalization_1810 (c1_sign : Int) : (((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) ↔ (((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := (iff_congr (normalization_1451 c1_sign) (normalization_1809 c1_sign))

-- Checked replay of rewrite.
theorem replay_362 (c1_sign : Int) : (((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_251 ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) ((c1_sign) ≤ (2 : Int)) ((c1_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1810 c1_sign) hn

abbrev formula_457 (c1_depth c1_kind c1_sign r0_level : Int) : Prop := ((¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))))

theorem normalized_252 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1811 (c1_depth c1_kind c1_sign r0_level : Int) : (formula_457 c1_depth c1_kind c1_sign r0_level) ↔ ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := (and_congr (normalization_1784 c1_kind) (and_congr (normalization_1794 c1_depth r0_level) (normalization_1809 c1_sign)))

theorem normalization_1812 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (formula_457 c1_depth c1_kind c1_sign r0_level)) ↔ (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))) := (iff_congr (normalization_1619 c1_depth c1_kind c1_sign r0_level) (normalization_1811 c1_depth c1_kind c1_sign r0_level))

-- Checked replay of monotonicity.
theorem replay_363 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (formula_457 c1_depth c1_kind c1_sign r0_level)) := by
  classical
  have ht := (normalized_252 (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))) ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))
  have n0 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1786 c1_kind) (replay_358 c1_kind)
  have n1 : (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_1796 c1_depth r0_level) (replay_361 c1_depth r0_level)
  have n2 : (((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_1810 c1_sign) (replay_362 c1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_1812 c1_depth c1_kind c1_sign r0_level) hn

theorem normalized_253 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1813 (c1_sign : Int) : (¬ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_1809 c1_sign))

theorem normalization_1814 (c1_depth c1_kind c1_sign r0_level : Int) : (formula_346 c1_depth c1_kind c1_sign r0_level) ↔ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1791 c1_depth r0_level) (or_congr (normalization_1792 c1_depth r0_level) (normalization_1813 c1_sign)))))

theorem normalization_1815 (c1_depth c1_kind c1_sign r0_level : Int) : (¬ (formula_346 c1_depth c1_kind c1_sign r0_level)) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))) := (not_congr (normalization_1814 c1_depth c1_kind c1_sign r0_level))

theorem normalization_1816 (c1_depth c1_kind c1_sign r0_level : Int) : ((formula_457 c1_depth c1_kind c1_sign r0_level) ↔ (¬ (formula_346 c1_depth c1_kind c1_sign r0_level))) ↔ (((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := (iff_congr (normalization_1811 c1_depth c1_kind c1_sign r0_level) (normalization_1815 c1_depth c1_kind c1_sign r0_level))

-- Checked replay of rewrite.
theorem replay_364 (c1_depth c1_kind c1_sign r0_level : Int) : ((formula_457 c1_depth c1_kind c1_sign r0_level) ↔ (¬ (formula_346 c1_depth c1_kind c1_sign r0_level))) := by
  classical
  have ht := (normalized_253 ((c1_kind) ≤ (1 : Int)) ((c1_kind) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_1816 c1_depth c1_kind c1_sign r0_level) hn

theorem normalized_254 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1817 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (¬ (formula_346 c1_depth c1_kind c1_sign r0_level))) ↔ (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := (iff_congr (normalization_1619 c1_depth c1_kind c1_sign r0_level) (normalization_1815 c1_depth c1_kind c1_sign r0_level))

-- Checked replay of trans.
theorem replay_365 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (0 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (¬ (formula_346 c1_depth c1_kind c1_sign r0_level))) := by
  classical
  have ht := (normalized_254 ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))
  have n0 : (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))) := by
    exact Iff.mp (normalization_1812 c1_depth c1_kind c1_sign r0_level) (replay_363 c1_depth c1_kind c1_sign r0_level)
  have n1 : (((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := by
    exact Iff.mp (normalization_1816 c1_depth c1_kind c1_sign r0_level) (replay_364 c1_depth c1_kind c1_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1817 c1_depth c1_kind c1_sign r0_level) hn

abbrev formula_458 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_346 c1_depth c1_kind c1_sign r0_level))))

theorem normalized_255 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1818 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : (formula_458 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_1774 c1_kind)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_1815 c1_depth c1_kind c1_sign r0_level)))

theorem normalization_1819 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_434 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_458 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))))) := (iff_congr (normalization_1620 c1_depth c1_kind c1_sign r0_group r0_level) (normalization_1818 c1_depth c1_kind c1_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_366 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_434 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_458 c1_depth c1_kind c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_255 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1776 c1_kind) (replay_355 c1_kind)
  have n2 : (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := by
    exact Iff.mp (normalization_1817 c1_depth c1_kind c1_sign r0_level) (replay_365 c1_depth c1_kind c1_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_1819 c1_depth c1_kind c1_sign r0_group r0_level) hn

theorem normalized_256 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1820 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : (formula_347 c1_depth c1_kind c1_sign r0_group r0_level) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_1815 c1_depth c1_kind c1_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_1774 c1_kind)))

theorem normalization_1821 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_458 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (iff_congr (normalization_1818 c1_depth c1_kind c1_sign r0_group r0_level) (normalization_1820 c1_depth c1_kind c1_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_367 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_458 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_256 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))
  have hn := ht
  exact Iff.mpr (normalization_1821 c1_depth c1_kind c1_sign r0_group r0_level) hn

theorem normalized_257 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1822 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_434 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (iff_congr (normalization_1620 c1_depth c1_kind c1_sign r0_group r0_level) (normalization_1820 c1_depth c1_kind c1_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_368 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_434 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_257 (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))
  have n0 : ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))))) := by
    exact Iff.mp (normalization_1819 c1_depth c1_kind c1_sign r0_group r0_level) (replay_366 c1_depth c1_kind c1_sign r0_group r0_level)
  have n1 : ((((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := by
    exact Iff.mp (normalization_1821 c1_depth c1_kind c1_sign r0_group r0_level) (replay_367 c1_depth c1_kind c1_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1822 c1_depth c1_kind c1_sign r0_group r0_level) hn

abbrev formula_459 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (0 : Int)) ∧ (formula_434 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))))) ∧ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)))

theorem normalized_258 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1823 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))))) ∧ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (and_congr (normalization_1754 r0_mode) (normalization_1820 c1_depth c1_kind c1_sign r0_group r0_level))

theorem normalization_1824 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_459 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) ↔ (((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ↔ ((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))) := (iff_congr (normalization_1621 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (normalization_1823 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_369 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_459 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_258 (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int))))) (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))
  have n0 : ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1756 r0_mode) (replay_349 r0_mode)
  have n1 : ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := by
    exact Iff.mp (normalization_1822 c1_depth c1_kind c1_sign r0_group r0_level) (replay_368 c1_depth c1_kind c1_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1824 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) hn

abbrev formula_460 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))))) ∧ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)))))

theorem normalized_259 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1825 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : (¬ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (not_congr (normalization_1820 c1_depth c1_kind c1_sign r0_group r0_level))

theorem normalization_1826 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level))) ↔ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))) := (or_congr (normalization_1752 r0_mode) (or_congr (normalization_1751 r0_mode) (normalization_1825 c1_depth c1_kind c1_sign r0_group r0_level)))

theorem normalization_1827 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)))) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))))) := (not_congr (normalization_1826 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

theorem normalization_1828 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_460 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) ↔ (((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))) := (iff_congr (normalization_1823 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (normalization_1827 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_370 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_460 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_259 ((r0_mode) ≤ (0 : Int)) ((r0_mode) ≤ (-1 : Int)) ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))
  have hn := ht
  exact Iff.mpr (normalization_1828 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) hn

abbrev formula_461 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (0 : Int)) ∧ (formula_434 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (formula_347 c1_depth c1_kind c1_sign r0_group r0_level)))))

theorem normalized_260 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1829 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_461 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) ↔ (((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))) := (iff_congr (normalization_1621 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (normalization_1827 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_371 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_461 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_260 ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))
  have n0 : (((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ↔ ((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))) := by
    exact Iff.mp (normalization_1824 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (replay_369 c1_depth c1_kind c1_sign r0_group r0_level r0_mode)
  have n1 : (((¬ ((¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))) := by
    exact Iff.mp (normalization_1828 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (replay_370 c1_depth c1_kind c1_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1829 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) hn

theorem normalized_261 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1830 (r0_mode : Int) : (r0_mode ≤ (1 : Int)) ↔ ((r0_mode) ≤ (1 : Int)) := by
  omega

theorem normalization_1831 (r0_mode : Int) : (r0_mode ≥ (1 : Int)) ↔ (¬ ((r0_mode) ≤ (0 : Int))) := by
  omega

theorem normalization_1832 (r0_mode : Int) : ((r0_mode ≤ (1 : Int)) ∧ (r0_mode ≥ (1 : Int))) ↔ (((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) := (and_congr (normalization_1830 r0_mode) (normalization_1831 r0_mode))

theorem normalization_1833 (r0_mode : Int) : ((r0_mode = (1 : Int)) ↔ ((r0_mode ≤ (1 : Int)) ∧ (r0_mode ≥ (1 : Int)))) ↔ ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int))))) := (iff_congr (normalization_1455 r0_mode) (normalization_1832 r0_mode))

-- Checked replay of rewrite.
theorem replay_372 (r0_mode : Int) : ((r0_mode = (1 : Int)) ↔ ((r0_mode ≤ (1 : Int)) ∧ (r0_mode ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_261 (((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_1833 r0_mode) hn

theorem normalized_262 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1834 (r0_mode : Int) : (¬ (r0_mode ≤ (1 : Int))) ↔ (¬ ((r0_mode) ≤ (1 : Int))) := (not_congr (normalization_1830 r0_mode))

theorem normalization_1835 (r0_mode : Int) : (¬ (r0_mode ≥ (1 : Int))) ↔ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) := (not_congr (normalization_1831 r0_mode))

theorem normalization_1836 (r0_mode : Int) : ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int)))) ↔ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))) := (or_congr (normalization_1834 r0_mode) (normalization_1835 r0_mode))

theorem normalization_1837 (r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) := (not_congr (normalization_1836 r0_mode))

theorem normalization_1838 (r0_mode : Int) : (((r0_mode ≤ (1 : Int)) ∧ (r0_mode ≥ (1 : Int))) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int)))))) ↔ ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))))) := (iff_congr (normalization_1832 r0_mode) (normalization_1837 r0_mode))

-- Checked replay of rewrite.
theorem replay_373 (r0_mode : Int) : (((r0_mode ≤ (1 : Int)) ∧ (r0_mode ≥ (1 : Int))) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_262 ((r0_mode) ≤ (1 : Int)) ((r0_mode) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1838 r0_mode) hn

theorem normalized_263 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1839 (r0_mode : Int) : ((r0_mode = (1 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int)))))) ↔ ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))))) := (iff_congr (normalization_1455 r0_mode) (normalization_1837 r0_mode))

-- Checked replay of trans.
theorem replay_374 (r0_mode : Int) : ((r0_mode = (1 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_263 (((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))))))
  have n0 : ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_1833 r0_mode) (replay_372 r0_mode)
  have n1 : ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1838 r0_mode) (replay_373 r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1839 r0_mode) hn

theorem normalized_264 (p0 p1 p2 : Prop) : (((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p0))) ↔ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p0)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1840 (c1_sign : Int) : (c1_sign ≤ (1 : Int)) ↔ ((c1_sign) ≤ (1 : Int)) := by
  omega

theorem normalization_1841 (c1_sign : Int) : (¬ (c1_sign ≤ (1 : Int))) ↔ (¬ ((c1_sign) ≤ (1 : Int))) := (not_congr (normalization_1840 c1_sign))

theorem normalization_1842 (c1_sign : Int) : (c1_sign ≥ (1 : Int)) ↔ (¬ ((c1_sign) ≤ (0 : Int))) := by
  omega

theorem normalization_1843 (c1_sign : Int) : (¬ (c1_sign ≥ (1 : Int))) ↔ (¬ (¬ ((c1_sign) ≤ (0 : Int)))) := (not_congr (normalization_1842 c1_sign))

theorem normalization_1844 (c1_sign : Int) : ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))) ↔ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) := (or_congr (normalization_1841 c1_sign) (normalization_1843 c1_sign))

theorem normalization_1845 (c1_sign : Int) : (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) := (not_congr (normalization_1844 c1_sign))

theorem normalization_1846 (c1_sign : Int) : ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))) := (or_congr (normalization_1845 c1_sign) (normalization_1808 c1_sign))

theorem normalization_1847 (c1_sign : Int) : (((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) ↔ (((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := (iff_congr (normalization_1457 c1_sign) (normalization_1846 c1_sign))

-- Checked replay of rewrite.
theorem replay_375 (c1_sign : Int) : (((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ↔ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_264 ((c1_sign) ≤ (1 : Int)) ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1847 c1_sign) hn

abbrev formula_462 (c1_depth c1_kind c1_sign r0_level : Int) : Prop := ((¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) ∧ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))))

theorem normalized_265 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → ((p0 ∧ p2 ∧ p4) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1848 (c1_depth c1_kind c1_sign r0_level : Int) : (formula_462 c1_depth c1_kind c1_sign r0_level) ↔ ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := (and_congr (normalization_1784 c1_kind) (and_congr (normalization_1794 c1_depth r0_level) (normalization_1846 c1_sign)))

theorem normalization_1849 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (formula_462 c1_depth c1_kind c1_sign r0_level)) ↔ (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))) := (iff_congr (normalization_1622 c1_depth c1_kind c1_sign r0_level) (normalization_1848 c1_depth c1_kind c1_sign r0_level))

-- Checked replay of monotonicity.
theorem replay_376 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (formula_462 c1_depth c1_kind c1_sign r0_level)) := by
  classical
  have ht := (normalized_265 (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))) ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))
  have n0 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1786 c1_kind) (replay_358 c1_kind)
  have n1 : (((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_1796 c1_depth r0_level) (replay_361 c1_depth r0_level)
  have n2 : (((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_1847 c1_sign) (replay_375 c1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_1849 c1_depth c1_kind c1_sign r0_level) hn

theorem normalized_266 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ (¬ p2)) ∨ (¬ p3))) ∧ p4) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ (¬ p2)) ∨ (¬ p3) ∨ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1850 (c1_sign : Int) : (¬ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_1846 c1_sign))

theorem normalization_1851 (c1_depth c1_kind c1_sign r0_level : Int) : (formula_348 c1_depth c1_kind c1_sign r0_level) ↔ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1791 c1_depth r0_level) (or_congr (normalization_1792 c1_depth r0_level) (normalization_1850 c1_sign)))))

theorem normalization_1852 (c1_depth c1_kind c1_sign r0_level : Int) : (¬ (formula_348 c1_depth c1_kind c1_sign r0_level)) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))) := (not_congr (normalization_1851 c1_depth c1_kind c1_sign r0_level))

theorem normalization_1853 (c1_depth c1_kind c1_sign r0_level : Int) : ((formula_462 c1_depth c1_kind c1_sign r0_level) ↔ (¬ (formula_348 c1_depth c1_kind c1_sign r0_level))) ↔ (((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := (iff_congr (normalization_1848 c1_depth c1_kind c1_sign r0_level) (normalization_1852 c1_depth c1_kind c1_sign r0_level))

-- Checked replay of rewrite.
theorem replay_377 (c1_depth c1_kind c1_sign r0_level : Int) : ((formula_462 c1_depth c1_kind c1_sign r0_level) ↔ (¬ (formula_348 c1_depth c1_kind c1_sign r0_level))) := by
  classical
  have ht := (normalized_266 ((c1_kind) ≤ (1 : Int)) ((c1_kind) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))
  have hn := ht
  exact Iff.mpr (normalization_1853 c1_depth c1_kind c1_sign r0_level) hn

theorem normalized_267 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1854 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (¬ (formula_348 c1_depth c1_kind c1_sign r0_level))) ↔ (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := (iff_congr (normalization_1622 c1_depth c1_kind c1_sign r0_level) (normalization_1852 c1_depth c1_kind c1_sign r0_level))

-- Checked replay of trans.
theorem replay_378 (c1_depth c1_kind c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) = (1 : Int)) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int)))) ↔ (¬ (formula_348 c1_depth c1_kind c1_sign r0_level))) := by
  classical
  have ht := (normalized_267 ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))
  have n0 : (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))) := by
    exact Iff.mp (normalization_1849 c1_depth c1_kind c1_sign r0_level) (replay_376 c1_depth c1_kind c1_sign r0_level)
  have n1 : (((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := by
    exact Iff.mp (normalization_1853 c1_depth c1_kind c1_sign r0_level) (replay_377 c1_depth c1_kind c1_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1854 c1_depth c1_kind c1_sign r0_level) hn

abbrev formula_463 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_348 c1_depth c1_kind c1_sign r0_level))))

theorem normalized_268 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1855 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : (formula_463 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_1774 c1_kind)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_1852 c1_depth c1_kind c1_sign r0_level)))

theorem normalization_1856 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_435 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_463 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))))) := (iff_congr (normalization_1623 c1_depth c1_kind c1_sign r0_group r0_level) (normalization_1855 c1_depth c1_kind c1_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_379 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_435 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_463 c1_depth c1_kind c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_268 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1776 c1_kind) (replay_355 c1_kind)
  have n2 : (((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) := by
    exact Iff.mp (normalization_1854 c1_depth c1_kind c1_sign r0_level) (replay_378 c1_depth c1_kind c1_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_1856 c1_depth c1_kind c1_sign r0_group r0_level) hn

theorem normalized_269 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1857 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : (formula_349 c1_depth c1_kind c1_sign r0_group r0_level) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_1852 c1_depth c1_kind c1_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_1774 c1_kind)))

theorem normalization_1858 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_463 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (iff_congr (normalization_1855 c1_depth c1_kind c1_sign r0_group r0_level) (normalization_1857 c1_depth c1_kind c1_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_380 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_463 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_269 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))
  have hn := ht
  exact Iff.mpr (normalization_1858 c1_depth c1_kind c1_sign r0_group r0_level) hn

theorem normalized_270 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1859 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_435 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (iff_congr (normalization_1623 c1_depth c1_kind c1_sign r0_group r0_level) (normalization_1857 c1_depth c1_kind c1_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_381 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : ((formula_435 c1_depth c1_kind c1_sign r0_group r0_level) ↔ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_270 (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))
  have n0 : ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))))) := by
    exact Iff.mp (normalization_1856 c1_depth c1_kind c1_sign r0_group r0_level) (replay_379 c1_depth c1_kind c1_sign r0_group r0_level)
  have n1 : ((((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := by
    exact Iff.mp (normalization_1858 c1_depth c1_kind c1_sign r0_group r0_level) (replay_380 c1_depth c1_kind c1_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1859 c1_depth c1_kind c1_sign r0_group r0_level) hn

abbrev formula_464 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (1 : Int)) ∧ (formula_435 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))))) ∧ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)))

theorem normalized_271 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1860 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))))) ∧ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (and_congr (normalization_1837 r0_mode) (normalization_1857 c1_depth c1_kind c1_sign r0_group r0_level))

theorem normalization_1861 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_464 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) ↔ (((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ↔ ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))) := (iff_congr (normalization_1624 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (normalization_1860 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_382 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_464 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_271 (((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))) (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))
  have n0 : ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1839 r0_mode) (replay_374 r0_mode)
  have n1 : ((((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))))))) ↔ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := by
    exact Iff.mp (normalization_1859 c1_depth c1_kind c1_sign r0_group r0_level) (replay_381 c1_depth c1_kind c1_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1861 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) hn

abbrev formula_465 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))))) ∧ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)))))

theorem normalized_272 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1862 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : (¬ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) := (not_congr (normalization_1857 c1_depth c1_kind c1_sign r0_group r0_level))

theorem normalization_1863 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level))) ↔ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))) := (or_congr (normalization_1834 r0_mode) (or_congr (normalization_1835 r0_mode) (normalization_1862 c1_depth c1_kind c1_sign r0_group r0_level)))

theorem normalization_1864 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))))) := (not_congr (normalization_1863 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

theorem normalization_1865 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_465 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) ↔ (((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))) := (iff_congr (normalization_1860 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (normalization_1864 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_383 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_465 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_272 ((r0_mode) ≤ (1 : Int)) ((r0_mode) ≤ (0 : Int)) ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))
  have hn := ht
  exact Iff.mpr (normalization_1865 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) hn

abbrev formula_466 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (1 : Int)) ∧ (formula_435 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (1 : Int))) ∨ (¬ (formula_349 c1_depth c1_kind c1_sign r0_group r0_level)))))

theorem normalized_273 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1866 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_466 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) ↔ (((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))) := (iff_congr (normalization_1624 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (normalization_1864 c1_depth c1_kind c1_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_384 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : (formula_466 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_273 ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))
  have n0 : (((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))))) ↔ ((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))) := by
    exact Iff.mp (normalization_1861 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (replay_382 c1_depth c1_kind c1_sign r0_group r0_level r0_mode)
  have n1 : (((¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))))) ∧ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))))))) := by
    exact Iff.mp (normalization_1865 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (replay_383 c1_depth c1_kind c1_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1866 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) hn

theorem normalized_274 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1867 (r0_mode : Int) : (r0_mode ≤ (2 : Int)) ↔ ((r0_mode) ≤ (2 : Int)) := by
  omega

theorem normalization_1868 (r0_mode : Int) : (r0_mode ≥ (2 : Int)) ↔ (¬ ((r0_mode) ≤ (1 : Int))) := by
  omega

theorem normalization_1869 (r0_mode : Int) : ((r0_mode ≤ (2 : Int)) ∧ (r0_mode ≥ (2 : Int))) ↔ (((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) := (and_congr (normalization_1867 r0_mode) (normalization_1868 r0_mode))

theorem normalization_1870 (r0_mode : Int) : ((r0_mode = (2 : Int)) ↔ ((r0_mode ≤ (2 : Int)) ∧ (r0_mode ≥ (2 : Int)))) ↔ ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ↔ (((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int))))) := (iff_congr (normalization_1461 r0_mode) (normalization_1869 r0_mode))

-- Checked replay of rewrite.
theorem replay_385 (r0_mode : Int) : ((r0_mode = (2 : Int)) ↔ ((r0_mode ≤ (2 : Int)) ∧ (r0_mode ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_274 (((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_1870 r0_mode) hn

theorem normalized_275 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1871 (r0_mode : Int) : (¬ (r0_mode ≤ (2 : Int))) ↔ (¬ ((r0_mode) ≤ (2 : Int))) := (not_congr (normalization_1867 r0_mode))

theorem normalization_1872 (r0_mode : Int) : (¬ (r0_mode ≥ (2 : Int))) ↔ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) := (not_congr (normalization_1868 r0_mode))

theorem normalization_1873 (r0_mode : Int) : ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int)))) ↔ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int))))) := (or_congr (normalization_1871 r0_mode) (normalization_1872 r0_mode))

theorem normalization_1874 (r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int))))) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))))) := (not_congr (normalization_1873 r0_mode))

theorem normalization_1875 (r0_mode : Int) : (((r0_mode ≤ (2 : Int)) ∧ (r0_mode ≥ (2 : Int))) ↔ (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int)))))) ↔ ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int))))))) := (iff_congr (normalization_1869 r0_mode) (normalization_1874 r0_mode))

-- Checked replay of rewrite.
theorem replay_386 (r0_mode : Int) : (((r0_mode ≤ (2 : Int)) ∧ (r0_mode ≥ (2 : Int))) ↔ (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_275 ((r0_mode) ≤ (2 : Int)) ((r0_mode) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1875 r0_mode) hn

theorem normalized_276 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1876 (r0_mode : Int) : ((r0_mode = (2 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int)))))) ↔ ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int))))))) := (iff_congr (normalization_1461 r0_mode) (normalization_1874 r0_mode))

-- Checked replay of trans.
theorem replay_387 (r0_mode : Int) : ((r0_mode = (2 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (2 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_276 (((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int))))))))
  have n0 : ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ↔ (((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_1870 r0_mode) (replay_385 r0_mode)
  have n1 : ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1875 r0_mode) (replay_386 r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1876 r0_mode) hn

theorem normalized_277 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1877 (c1_depth r0_level : Int) : (c1_depth ≤ r0_level) ↔ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_1878 (c1_depth r0_level : Int) : (c1_depth ≥ r0_level) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_1879 (c1_depth r0_level : Int) : ((c1_depth ≤ r0_level) ∧ (c1_depth ≥ r0_level)) ↔ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (and_congr (normalization_1877 c1_depth r0_level) (normalization_1878 c1_depth r0_level))

theorem normalization_1880 (c1_depth r0_level : Int) : ((c1_depth = r0_level) ↔ ((c1_depth ≤ r0_level) ∧ (c1_depth ≥ r0_level))) ↔ ((((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ↔ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) := (iff_congr (normalization_1462 c1_depth r0_level) (normalization_1879 c1_depth r0_level))

-- Checked replay of rewrite.
theorem replay_388 (c1_depth r0_level : Int) : ((c1_depth = r0_level) ↔ ((c1_depth ≤ r0_level) ∧ (c1_depth ≥ r0_level))) := by
  classical
  have ht := (normalized_277 (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_1880 c1_depth r0_level) hn

theorem normalized_278 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1881 (c1_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_1882 (c1_depth r0_level : Int) : ((c1_depth ≤ r0_level) ↔ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := (iff_congr (normalization_1877 c1_depth r0_level) (normalization_1881 c1_depth r0_level))

-- Checked replay of rewrite.
theorem replay_389 (c1_depth r0_level : Int) : ((c1_depth ≤ r0_level) ↔ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_278 ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1882 c1_depth r0_level) hn

theorem normalized_279 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1883 (c1_depth r0_level : Int) : ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_1884 (c1_depth r0_level : Int) : ((c1_depth ≥ r0_level) ↔ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (iff_congr (normalization_1878 c1_depth r0_level) (normalization_1883 c1_depth r0_level))

-- Checked replay of rewrite.
theorem replay_390 (c1_depth r0_level : Int) : ((c1_depth ≥ r0_level) ↔ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_279 ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1884 c1_depth r0_level) hn

theorem normalized_280 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1885 (c1_depth r0_level : Int) : (((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (and_congr (normalization_1881 c1_depth r0_level) (normalization_1883 c1_depth r0_level))

theorem normalization_1886 (c1_depth r0_level : Int) : (((c1_depth ≤ r0_level) ∧ (c1_depth ≥ r0_level)) ↔ (((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) ↔ ((((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ↔ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) := (iff_congr (normalization_1879 c1_depth r0_level) (normalization_1885 c1_depth r0_level))

-- Checked replay of monotonicity.
theorem replay_391 (c1_depth r0_level : Int) : (((c1_depth ≤ r0_level) ∧ (c1_depth ≥ r0_level)) ↔ (((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ∧ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_280 ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))
  have n0 : (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_1882 c1_depth r0_level) (replay_389 c1_depth r0_level)
  have n1 : ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_1884 c1_depth r0_level) (replay_390 c1_depth r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1886 c1_depth r0_level) hn

end H4Formal.Generated.Repair
