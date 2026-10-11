import H4Formal.Certificates.CheckedClassification.Classification026

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_764 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3517 (c0_kind : Int) : ((c0_kind = (0 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) ↔ ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) := (iff_congr (normalization_3209 c0_kind) (normalization_3515 c0_kind))

-- Checked replay of trans.
theorem replay_1292 (c0_kind : Int) : ((c0_kind = (0 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_764 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))))
  have n0 : ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_3511 c0_kind) (replay_1290 c0_kind)
  have n1 : ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3516 c0_kind) (replay_1291 c0_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3517 c0_kind) hn

abbrev shared_expr_Classification027_0 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_960 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) ↔ ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_182 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_969 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (shared_expr_Classification027_0 c0_group c0_level c0_mode c2_group c2_level c2_mode)

theorem normalized_765 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3518 (c0_level c2_level : Int) : ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_3519 (c0_level c2_level : Int) : (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := (not_congr (normalization_3518 c0_level c2_level))

theorem normalization_3520 (c0_level c2_level : Int) : ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) := (or_congr (normalization_3519 c0_level c2_level) (normalization_3482 c0_level c2_level))

theorem normalization_3521 (c0_mode c2_mode : Int) : ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_3522 (c0_mode c2_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) := (not_congr (normalization_3521 c0_mode c2_mode))

theorem normalization_3523 (c0_mode c2_mode : Int) : ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_3522 c0_mode c2_mode) (normalization_3479 c0_mode c2_mode))

abbrev shared_expr_Classification027_1 (c0_group c0_mode c2_group c2_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))))
theorem normalization_3524 (c0_group c0_mode c2_group c2_mode : Int) : (formula_181 c0_group c0_mode c2_group c2_mode) ↔ (shared_expr_Classification027_1 c0_group c0_mode c2_group c2_mode) := (or_congr (and_congr (normalization_3523 c0_mode c2_mode) (normalization_3479 c0_mode c2_mode)) (and_congr (not_congr (normalization_3523 c0_mode c2_mode)) (normalization_3477 c0_group c2_group)))

abbrev shared_expr_Classification027_2 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification027_1 c0_group c0_mode c2_group c2_mode)))
theorem normalization_3525 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_182 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Classification027_2 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_3520 c0_level c2_level) (normalization_3482 c0_level c2_level)) (and_congr (not_congr (normalization_3520 c0_level c2_level)) (normalization_3524 c0_group c0_mode c2_group c2_mode)))

abbrev shared_expr_Classification027_3 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification027_2 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_3526 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_182 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) ↔ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_3442 c0_mode c2_mode) (normalization_3525 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (and_congr (not_congr (normalization_3442 c0_mode c2_mode)) (normalization_3411 c0_mode)))

abbrev shared_expr_Classification027_4 (c0_group c0_mode c2_group c2_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification027_5 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification027_4 c0_group c0_mode c2_group c2_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Classification027_6 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification027_5 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_3527 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_969 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ ((shared_expr_Classification027_6 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (iff_congr (normalization_3484 c0_group c0_level c0_mode c2_group c2_level c2_mode) (normalization_3526 c0_group c0_level c0_mode c2_group c2_level c2_mode))

-- Checked replay of rewrite.
theorem replay_1293 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_969 c0_group c0_level c0_mode c2_group c2_level c2_mode) := by
  classical
  have ht := (normalized_765 ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)) ((c0_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3527 c0_group c0_level c0_mode c2_group c2_level c2_mode) hn

abbrev shared_expr_Classification027_7 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_182 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_970 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (shared_expr_Classification027_7 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)

theorem normalized_766 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3528 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_970 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (or_congr (normalization_889 c2_kind) (normalization_3526 c0_group c0_level c0_mode c2_group c2_level c2_mode))

abbrev shared_expr_Classification027_8 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_6 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem normalization_3529 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_961 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_970 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Classification027_8 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_3485 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (normalization_3528 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of monotonicity.
theorem replay_1294 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_961 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_970 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_766 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Classification027_6 c0_group c0_level c0_mode c2_group c2_level c2_mode) (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode))
  have n0 : ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_1956 c2_kind) (replay_686 c2_kind)
  have n1 : ((shared_expr_Classification027_6 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := by
    exact Iff.mp (normalization_3527 c0_group c0_level c0_mode c2_group c2_level c2_mode) (replay_1293 c0_group c0_level c0_mode c2_group c2_level c2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3529 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_767 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3530 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_944 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (or_congr (normalization_887 c2_kind) (or_congr (normalization_888 c2_kind) (normalization_3526 c0_group c0_level c0_mode c2_group c2_level c2_mode)))

abbrev shared_expr_Classification027_9 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem normalization_3531 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_970 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_944 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Classification027_9 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_3528 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (normalization_3530 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of rewrite.
theorem replay_1295 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_970 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_944 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_767 ((c2_kind) ≤ (0 : Int)) ((c2_kind) ≤ (-1 : Int)) (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode))
  have hn := ht
  exact Iff.mpr (normalization_3531 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_768 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_10 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_6 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem normalization_3532 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_961 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_944 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Classification027_10 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_3485 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (normalization_3530 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of trans.
theorem replay_1296 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_961 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_944 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_768 ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_6 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification027_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
  have n0 : (shared_expr_Classification027_8 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_3529 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (replay_1294 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)
  have n1 : (shared_expr_Classification027_9 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_3531 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (replay_1295 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3532 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_769 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3533 (c0_kind : Int) : (c0_kind ≤ (2 : Int)) ↔ ((c0_kind) ≤ (2 : Int)) := by
  omega

theorem normalization_3534 (c0_kind : Int) : (c0_kind ≥ (2 : Int)) ↔ (¬ ((c0_kind) ≤ (1 : Int))) := by
  omega

theorem normalization_3535 (c0_kind : Int) : ((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int))) ↔ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) := (and_congr (normalization_3533 c0_kind) (normalization_3534 c0_kind))

theorem normalization_3536 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ ((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int)))) ↔ ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) := (iff_congr (normalization_3214 c0_kind) (normalization_3535 c0_kind))

-- Checked replay of rewrite.
theorem replay_1297 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ ((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_769 (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3536 c0_kind) hn

theorem normalized_770 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3537 (c0_kind : Int) : (¬ (c0_kind ≤ (2 : Int))) ↔ (¬ ((c0_kind) ≤ (2 : Int))) := (not_congr (normalization_3533 c0_kind))

theorem normalization_3538 (c0_kind : Int) : (¬ (c0_kind ≥ (2 : Int))) ↔ (¬ (¬ ((c0_kind) ≤ (1 : Int)))) := (not_congr (normalization_3534 c0_kind))

theorem normalization_3539 (c0_kind : Int) : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) ↔ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) := (or_congr (normalization_3537 c0_kind) (normalization_3538 c0_kind))

theorem normalization_3540 (c0_kind : Int) : (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int)))))) := (not_congr (normalization_3539 c0_kind))

theorem normalization_3541 (c0_kind : Int) : (((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ↔ ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_3535 c0_kind) (normalization_3540 c0_kind))

-- Checked replay of rewrite.
theorem replay_1298 (c0_kind : Int) : (((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_770 ((c0_kind) ≤ (2 : Int)) ((c0_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3541 c0_kind) hn

theorem normalized_771 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3542 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ↔ ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_3214 c0_kind) (normalization_3540 c0_kind))

-- Checked replay of trans.
theorem replay_1299 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_771 (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
  have n0 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_3536 c0_kind) (replay_1297 c0_kind)
  have n1 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3541 c0_kind) (replay_1298 c0_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3542 c0_kind) hn

theorem normalized_772 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3543 (c0_depth c2_depth : Int) : (c0_depth ≤ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_3544 (c0_depth c2_depth : Int) : (c0_depth ≥ c2_depth) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3545 (c0_depth c2_depth : Int) : ((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_3543 c0_depth c2_depth) (normalization_3544 c0_depth c2_depth))

abbrev shared_expr_Classification027_11 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
theorem normalization_3546 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ ((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth))) ↔ (shared_expr_Classification027_11 c0_depth c2_depth) := (iff_congr (normalization_3422 c0_depth c2_depth) (normalization_3545 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1300 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ ((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth))) := by
  classical
  have ht := (normalized_772 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3546 c0_depth c2_depth) hn

theorem normalized_773 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3547 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_3548 (c0_depth c2_depth : Int) : ((c0_depth ≤ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := (iff_congr (normalization_3543 c0_depth c2_depth) (normalization_3547 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1301 (c0_depth c2_depth : Int) : ((c0_depth ≤ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_773 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3548 c0_depth c2_depth) hn

theorem normalized_774 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3549 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3550 (c0_depth c2_depth : Int) : ((c0_depth ≥ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_3544 c0_depth c2_depth) (normalization_3549 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1302 (c0_depth c2_depth : Int) : ((c0_depth ≥ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_774 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3550 c0_depth c2_depth) hn

theorem normalized_775 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3551 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_3547 c0_depth c2_depth) (normalization_3549 c0_depth c2_depth))

theorem normalization_3552 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification027_11 c0_depth c2_depth) := (iff_congr (normalization_3545 c0_depth c2_depth) (normalization_3551 c0_depth c2_depth))

-- Checked replay of monotonicity.
theorem replay_1303 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_775 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
  have n0 : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3548 c0_depth c2_depth) (replay_1301 c0_depth c2_depth)
  have n1 : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3550 c0_depth c2_depth) (replay_1302 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3552 c0_depth c2_depth) hn

abbrev shared_expr_Classification027_12 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))))
abbrev formula_971 (c0_depth c2_depth : Int) : Prop := (shared_expr_Classification027_12 c0_depth c2_depth)

theorem normalized_776 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3553 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := (not_congr (normalization_3547 c0_depth c2_depth))

theorem normalization_3554 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_3549 c0_depth c2_depth))

theorem normalization_3555 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_3553 c0_depth c2_depth) (normalization_3554 c0_depth c2_depth))

theorem normalization_3556 (c0_depth c2_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_3555 c0_depth c2_depth))

abbrev shared_expr_Classification027_13 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))))
theorem normalization_3557 (c0_depth c2_depth : Int) : (formula_971 c0_depth c2_depth) ↔ (shared_expr_Classification027_13 c0_depth c2_depth) := (iff_congr (normalization_3551 c0_depth c2_depth) (normalization_3556 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1304 (c0_depth c2_depth : Int) : (formula_971 c0_depth c2_depth) := by
  classical
  have ht := (normalized_776 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3557 c0_depth c2_depth) hn

theorem normalized_777 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3558 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification027_13 c0_depth c2_depth) := (iff_congr (normalization_3545 c0_depth c2_depth) (normalization_3556 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_1305 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_777 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Classification027_13 c0_depth c2_depth))
  have n0 : (shared_expr_Classification027_11 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3552 c0_depth c2_depth) (replay_1303 c0_depth c2_depth)
  have n1 : (shared_expr_Classification027_13 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3557 c0_depth c2_depth) (replay_1304 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3558 c0_depth c2_depth) hn

theorem normalized_778 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3559 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification027_13 c0_depth c2_depth) := (iff_congr (normalization_3422 c0_depth c2_depth) (normalization_3556 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_1306 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_778 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Classification027_13 c0_depth c2_depth))
  have n0 : (shared_expr_Classification027_11 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3546 c0_depth c2_depth) (replay_1300 c0_depth c2_depth)
  have n1 : (shared_expr_Classification027_13 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3558 c0_depth c2_depth) (replay_1305 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3559 c0_depth c2_depth) hn

theorem normalized_779 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3560 (c0_node c2_node : Int) : (c0_node ≤ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3561 (c0_node c2_node : Int) : (c0_node ≥ c2_node) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3562 (c0_node c2_node : Int) : ((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_3560 c0_node c2_node) (normalization_3561 c0_node c2_node))

abbrev shared_expr_Classification027_14 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_3563 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ ((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node))) ↔ (shared_expr_Classification027_14 c0_node c2_node) := (iff_congr (normalization_3423 c0_node c2_node) (normalization_3562 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_1307 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ ((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node))) := by
  classical
  have ht := (normalized_779 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3563 c0_node c2_node) hn

theorem normalized_780 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3564 (c0_node c2_node : Int) : ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3565 (c0_node c2_node : Int) : ((c0_node ≤ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (iff_congr (normalization_3560 c0_node c2_node) (normalization_3564 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_1308 (c0_node c2_node : Int) : ((c0_node ≤ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_780 ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3565 c0_node c2_node) hn

theorem normalized_781 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3566 (c0_node c2_node : Int) : ((c0_node ≥ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_3561 c0_node c2_node) (normalization_3486 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_1309 (c0_node c2_node : Int) : ((c0_node ≥ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_781 ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3566 c0_node c2_node) hn

theorem normalized_782 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3567 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_3564 c0_node c2_node) (normalization_3486 c0_node c2_node))

theorem normalization_3568 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification027_14 c0_node c2_node) := (iff_congr (normalization_3562 c0_node c2_node) (normalization_3567 c0_node c2_node))

-- Checked replay of monotonicity.
theorem replay_1310 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_782 ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
  have n0 : (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3565 c0_node c2_node) (replay_1308 c0_node c2_node)
  have n1 : ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3566 c0_node c2_node) (replay_1309 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3568 c0_node c2_node) hn

abbrev shared_expr_Classification027_15 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))))
abbrev formula_972 (c0_node c2_node : Int) : Prop := (shared_expr_Classification027_15 c0_node c2_node)

theorem normalized_783 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3569 (c0_node c2_node : Int) : (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_3564 c0_node c2_node))

theorem normalization_3570 (c0_node c2_node : Int) : ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) := (or_congr (normalization_3569 c0_node c2_node) (normalization_3487 c0_node c2_node))

theorem normalization_3571 (c0_node c2_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_3570 c0_node c2_node))

abbrev shared_expr_Classification027_16 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))))
theorem normalization_3572 (c0_node c2_node : Int) : (formula_972 c0_node c2_node) ↔ (shared_expr_Classification027_16 c0_node c2_node) := (iff_congr (normalization_3567 c0_node c2_node) (normalization_3571 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_1311 (c0_node c2_node : Int) : (formula_972 c0_node c2_node) := by
  classical
  have ht := (normalized_783 ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3572 c0_node c2_node) hn

theorem normalized_784 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3573 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification027_16 c0_node c2_node) := (iff_congr (normalization_3562 c0_node c2_node) (normalization_3571 c0_node c2_node))

-- Checked replay of trans.
theorem replay_1312 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_784 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) (shared_expr_Classification027_16 c0_node c2_node))
  have n0 : (shared_expr_Classification027_14 c0_node c2_node) := by
    exact Iff.mp (normalization_3568 c0_node c2_node) (replay_1310 c0_node c2_node)
  have n1 : (shared_expr_Classification027_16 c0_node c2_node) := by
    exact Iff.mp (normalization_3572 c0_node c2_node) (replay_1311 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3573 c0_node c2_node) hn

theorem normalized_785 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3574 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification027_16 c0_node c2_node) := (iff_congr (normalization_3423 c0_node c2_node) (normalization_3571 c0_node c2_node))

-- Checked replay of trans.
theorem replay_1313 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_785 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) (shared_expr_Classification027_16 c0_node c2_node))
  have n0 : (shared_expr_Classification027_14 c0_node c2_node) := by
    exact Iff.mp (normalization_3563 c0_node c2_node) (replay_1307 c0_node c2_node)
  have n1 : (shared_expr_Classification027_16 c0_node c2_node) := by
    exact Iff.mp (normalization_3573 c0_node c2_node) (replay_1312 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3574 c0_node c2_node) hn

theorem normalized_786 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3575 (c0_sign : Int) : (c0_sign ≤ (0 : Int)) ↔ ((c0_sign) ≤ (0 : Int)) := by
  omega

theorem normalization_3576 (c0_sign : Int) : (c0_sign ≥ (0 : Int)) ↔ (¬ ((c0_sign) ≤ (-1 : Int))) := by
  omega

theorem normalization_3577 (c0_sign : Int) : ((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int))) ↔ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) := (and_congr (normalization_3575 c0_sign) (normalization_3576 c0_sign))

theorem normalization_3578 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ ((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int)))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_3217 c0_sign) (normalization_3577 c0_sign))

-- Checked replay of rewrite.
theorem replay_1314 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ ((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_786 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3578 c0_sign) hn

theorem normalized_787 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3579 (c0_sign : Int) : (¬ (c0_sign ≤ (0 : Int))) ↔ (¬ ((c0_sign) ≤ (0 : Int))) := (not_congr (normalization_3575 c0_sign))

theorem normalization_3580 (c0_sign : Int) : (¬ (c0_sign ≥ (0 : Int))) ↔ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) := (not_congr (normalization_3576 c0_sign))

theorem normalization_3581 (c0_sign : Int) : ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))) ↔ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) := (or_congr (normalization_3579 c0_sign) (normalization_3580 c0_sign))

theorem normalization_3582 (c0_sign : Int) : (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) := (not_congr (normalization_3581 c0_sign))

theorem normalization_3583 (c0_sign : Int) : (((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_3577 c0_sign) (normalization_3582 c0_sign))

-- Checked replay of rewrite.
theorem replay_1315 (c0_sign : Int) : (((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_787 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3583 c0_sign) hn

theorem normalized_788 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3584 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_3217 c0_sign) (normalization_3582 c0_sign))

-- Checked replay of trans.
theorem replay_1316 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_788 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_3578 c0_sign) (replay_1314 c0_sign)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3583 c0_sign) (replay_1315 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3584 c0_sign) hn

theorem normalized_789 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3585 (c0_sign c2_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := (and_congr (normalization_3582 c0_sign) (normalization_1006 c2_sign))

abbrev shared_expr_Classification027_17 (c0_sign c2_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))))
theorem normalization_3586 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) ↔ (shared_expr_Classification027_17 c0_sign c2_sign) := (iff_congr (normalization_3424 c0_sign c2_sign) (normalization_3585 c0_sign c2_sign))

-- Checked replay of monotonicity.
theorem replay_1317 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_789 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1170 c2_sign) (replay_544 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3586 c0_sign c2_sign) hn

abbrev shared_expr_Classification027_18 (c0_sign c2_sign : Int) : Prop := (((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev formula_973 (c0_sign c2_sign : Int) : Prop := (shared_expr_Classification027_18 c0_sign c2_sign)

theorem normalized_790 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3587 (c0_sign c2_sign : Int) : ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ↔ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) := (or_congr (normalization_3579 c0_sign) (or_congr (normalization_3580 c0_sign) (or_congr (normalization_1002 c2_sign) (normalization_1004 c2_sign))))

theorem normalization_3588 (c0_sign c2_sign : Int) : (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) := (not_congr (normalization_3587 c0_sign c2_sign))

abbrev shared_expr_Classification027_19 (c0_sign c2_sign : Int) : Prop := (((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
theorem normalization_3589 (c0_sign c2_sign : Int) : (formula_973 c0_sign c2_sign) ↔ (shared_expr_Classification027_19 c0_sign c2_sign) := (iff_congr (normalization_3585 c0_sign c2_sign) (normalization_3588 c0_sign c2_sign))

-- Checked replay of rewrite.
theorem replay_1318 (c0_sign c2_sign : Int) : (formula_973 c0_sign c2_sign) := by
  classical
  have ht := (normalized_790 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3589 c0_sign c2_sign) hn

theorem normalized_791 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_20 (c0_sign c2_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
theorem normalization_3590 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ (shared_expr_Classification027_20 c0_sign c2_sign) := (iff_congr (normalization_3424 c0_sign c2_sign) (normalization_3588 c0_sign c2_sign))

-- Checked replay of trans.
theorem replay_1319 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_791 ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification027_17 c0_sign c2_sign) := by
    exact Iff.mp (normalization_3586 c0_sign c2_sign) (replay_1317 c0_sign c2_sign)
  have n1 : (shared_expr_Classification027_19 c0_sign c2_sign) := by
    exact Iff.mp (normalization_3589 c0_sign c2_sign) (replay_1318 c0_sign c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3590 c0_sign c2_sign) hn

abbrev shared_expr_Classification027_21 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification027_22 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Classification027_21 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))
abbrev formula_974 (c0_node c0_sign c2_node c2_sign : Int) : Prop := (shared_expr_Classification027_22 c0_node c0_sign c2_node c2_sign)

abbrev shared_expr_Classification027_23 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (formula_974 c0_node c0_sign c2_node c2_sign))
abbrev formula_975 (c0_node c0_sign c2_node c2_sign : Int) : Prop := (shared_expr_Classification027_23 c0_node c0_sign c2_node c2_sign)

theorem normalized_792 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_24 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification027_25 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Classification027_24 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
theorem normalization_3591 (c0_node c0_sign c2_node c2_sign : Int) : (formula_974 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Classification027_25 c0_node c0_sign c2_node c2_sign) := (or_congr (and_congr (normalization_3571 c0_node c2_node) (normalization_3588 c0_sign c2_sign)) (and_congr (not_congr (normalization_3571 c0_node c2_node)) (normalization_3487 c0_node c2_node)))

abbrev shared_expr_Classification027_26 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification027_27 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Classification027_26 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
theorem normalization_3592 (c0_node c0_sign c2_node c2_sign : Int) : (formula_975 c0_node c0_sign c2_node c2_sign) ↔ ((shared_expr_Classification027_27 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Classification027_25 c0_node c0_sign c2_node c2_sign)) := (iff_congr (normalization_3488 c0_node c0_sign c2_node c2_sign) (normalization_3591 c0_node c0_sign c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_1320 (c0_node c0_sign c2_node c2_sign : Int) : (formula_975 c0_node c0_sign c2_node c2_sign) := by
  classical
  have ht := (normalized_792 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification027_16 c0_node c2_node) := by
    exact Iff.mp (normalization_3574 c0_node c2_node) (replay_1313 c0_node c2_node)
  have n1 : (shared_expr_Classification027_20 c0_sign c2_sign) := by
    exact Iff.mp (normalization_3590 c0_sign c2_sign) (replay_1319 c0_sign c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3592 c0_node c0_sign c2_node c2_sign) hn

theorem normalized_793 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_28 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_24 c0_node c0_sign c2_node c2_sign))
theorem normalization_3593 (c0_node c0_sign c2_node c2_sign : Int) : (formula_941 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Classification027_28 c0_node c0_sign c2_node c2_sign) := (or_congr (and_congr (normalization_3570 c0_node c2_node) (normalization_3487 c0_node c2_node)) (and_congr (not_congr (normalization_3570 c0_node c2_node)) (normalization_3588 c0_sign c2_sign)))

theorem normalization_3594 (c0_node c0_sign c2_node c2_sign : Int) : ((formula_974 c0_node c0_sign c2_node c2_sign) ↔ (formula_941 c0_node c0_sign c2_node c2_sign)) ↔ ((shared_expr_Classification027_25 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Classification027_28 c0_node c0_sign c2_node c2_sign)) := (iff_congr (normalization_3591 c0_node c0_sign c2_node c2_sign) (normalization_3593 c0_node c0_sign c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_1321 (c0_node c0_sign c2_node c2_sign : Int) : ((formula_974 c0_node c0_sign c2_node c2_sign) ↔ (formula_941 c0_node c0_sign c2_node c2_sign)) := by
  classical
  have ht := (normalized_793 ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3594 c0_node c0_sign c2_node c2_sign) hn

abbrev shared_expr_Classification027_29 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (formula_941 c0_node c0_sign c2_node c2_sign))
abbrev formula_976 (c0_node c0_sign c2_node c2_sign : Int) : Prop := (shared_expr_Classification027_29 c0_node c0_sign c2_node c2_sign)

theorem normalized_794 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3595 (c0_node c0_sign c2_node c2_sign : Int) : (formula_976 c0_node c0_sign c2_node c2_sign) ↔ ((shared_expr_Classification027_27 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Classification027_28 c0_node c0_sign c2_node c2_sign)) := (iff_congr (normalization_3488 c0_node c0_sign c2_node c2_sign) (normalization_3593 c0_node c0_sign c2_node c2_sign))

-- Checked replay of trans.
theorem replay_1322 (c0_node c0_sign c2_node c2_sign : Int) : (formula_976 c0_node c0_sign c2_node c2_sign) := by
  classical
  have ht := (normalized_794 (shared_expr_Classification027_27 c0_node c0_sign c2_node c2_sign) (shared_expr_Classification027_25 c0_node c0_sign c2_node c2_sign) (shared_expr_Classification027_28 c0_node c0_sign c2_node c2_sign))
  have n0 : ((shared_expr_Classification027_27 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Classification027_25 c0_node c0_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_3592 c0_node c0_sign c2_node c2_sign) (replay_1320 c0_node c0_sign c2_node c2_sign)
  have n1 : ((shared_expr_Classification027_25 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Classification027_28 c0_node c0_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_3594 c0_node c0_sign c2_node c2_sign) (replay_1321 c0_node c0_sign c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3595 c0_node c0_sign c2_node c2_sign) hn

theorem normalized_795 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3596 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_3597 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_3598 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_3596 c0_depth c2_depth) (normalization_3597 c0_depth c2_depth))

abbrev shared_expr_Classification027_30 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))
theorem normalization_3599 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Classification027_30 c0_depth c2_depth) := (iff_congr (normalization_3489 c0_depth c2_depth) (normalization_3598 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1323 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_795 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3599 c0_depth c2_depth) hn

abbrev shared_expr_Classification027_31 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))))
abbrev formula_977 (c0_depth c2_depth : Int) : Prop := (shared_expr_Classification027_31 c0_depth c2_depth)

theorem normalized_796 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3600 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := (not_congr (normalization_3596 c0_depth c2_depth))

theorem normalization_3601 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_3597 c0_depth c2_depth))

theorem normalization_3602 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_3600 c0_depth c2_depth) (normalization_3601 c0_depth c2_depth))

theorem normalization_3603 (c0_depth c2_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_3602 c0_depth c2_depth))

abbrev shared_expr_Classification027_32 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))))
theorem normalization_3604 (c0_depth c2_depth : Int) : (formula_977 c0_depth c2_depth) ↔ (shared_expr_Classification027_32 c0_depth c2_depth) := (iff_congr (normalization_3598 c0_depth c2_depth) (normalization_3603 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1324 (c0_depth c2_depth : Int) : (formula_977 c0_depth c2_depth) := by
  classical
  have ht := (normalized_796 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3604 c0_depth c2_depth) hn

theorem normalized_797 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3605 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Classification027_32 c0_depth c2_depth) := (iff_congr (normalization_3489 c0_depth c2_depth) (normalization_3603 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_1325 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_797 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) (shared_expr_Classification027_32 c0_depth c2_depth))
  have n0 : (shared_expr_Classification027_30 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3599 c0_depth c2_depth) (replay_1323 c0_depth c2_depth)
  have n1 : (shared_expr_Classification027_32 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3604 c0_depth c2_depth) (replay_1324 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3605 c0_depth c2_depth) hn

theorem normalized_798 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3606 (c0_node c2_node : Int) : ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3607 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (and_congr (normalization_3606 c0_node c2_node) (normalization_3491 c0_node c2_node))

abbrev shared_expr_Classification027_33 (c0_node c2_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3608 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification027_33 c0_node c2_node) := (iff_congr (normalization_3490 c0_node c2_node) (normalization_3607 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_1326 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_798 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3608 c0_node c2_node) hn

abbrev shared_expr_Classification027_34 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_978 (c0_node c2_node : Int) : Prop := (shared_expr_Classification027_34 c0_node c2_node)

theorem normalized_799 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3609 (c0_node c2_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_3606 c0_node c2_node))

theorem normalization_3610 (c0_node c2_node : Int) : ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) := (or_congr (normalization_3609 c0_node c2_node) (normalization_3492 c0_node c2_node))

theorem normalization_3611 (c0_node c2_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) := (not_congr (normalization_3610 c0_node c2_node))

abbrev shared_expr_Classification027_35 (c0_node c2_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
theorem normalization_3612 (c0_node c2_node : Int) : (formula_978 c0_node c2_node) ↔ (shared_expr_Classification027_35 c0_node c2_node) := (iff_congr (normalization_3607 c0_node c2_node) (normalization_3611 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_1327 (c0_node c2_node : Int) : (formula_978 c0_node c2_node) := by
  classical
  have ht := (normalized_799 (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3612 c0_node c2_node) hn

abbrev shared_expr_Classification027_36 (c0_node c2_node : Int) : Prop := (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_979 (c0_node c2_node : Int) : Prop := (shared_expr_Classification027_36 c0_node c2_node)

theorem normalized_800 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3613 (c0_node c2_node : Int) : (formula_979 c0_node c2_node) ↔ (shared_expr_Classification027_35 c0_node c2_node) := (iff_congr (normalization_3490 c0_node c2_node) (normalization_3611 c0_node c2_node))

-- Checked replay of trans.
theorem replay_1328 (c0_node c2_node : Int) : (formula_979 c0_node c2_node) := by
  classical
  have ht := (normalized_800 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) (shared_expr_Classification027_35 c0_node c2_node))
  have n0 : (shared_expr_Classification027_33 c0_node c2_node) := by
    exact Iff.mp (normalization_3608 c0_node c2_node) (replay_1326 c0_node c2_node)
  have n1 : (shared_expr_Classification027_35 c0_node c2_node) := by
    exact Iff.mp (normalization_3612 c0_node c2_node) (replay_1327 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3613 c0_node c2_node) hn

abbrev shared_expr_Classification027_37 (c0_node c0_sign c2_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev shared_expr_Classification027_38 (c0_node c2_node : Int) : Prop := ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_980 (c0_node c0_sign c2_node : Int) : Prop := ((shared_expr_Classification027_37 c0_node c0_sign c2_node) ∨ (shared_expr_Classification027_38 c0_node c2_node))

theorem normalized_801 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_39 (c0_node c0_sign c2_node : Int) : Prop := ((¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Classification027_40 (c0_node c2_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3614 (c0_node c0_sign c2_node : Int) : (formula_980 c0_node c0_sign c2_node) ↔ ((shared_expr_Classification027_39 c0_node c0_sign c2_node) ∨ (shared_expr_Classification027_40 c0_node c2_node)) := (or_congr (and_congr (normalization_3611 c0_node c2_node) (normalization_3582 c0_sign)) (and_congr (not_congr (normalization_3611 c0_node c2_node)) (normalization_3492 c0_node c2_node)))

abbrev shared_expr_Classification027_41 (c0_node c2_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification027_42 (c0_node c0_sign c2_node : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification027_41 c0_node c2_node))
theorem normalization_3615 (c0_node c0_sign c2_node : Int) : ((formula_962 c0_node c0_sign c2_node) ↔ (formula_980 c0_node c0_sign c2_node)) ↔ ((shared_expr_Classification027_42 c0_node c0_sign c2_node) ↔ ((shared_expr_Classification027_39 c0_node c0_sign c2_node) ∨ (shared_expr_Classification027_40 c0_node c2_node))) := (iff_congr (normalization_3493 c0_node c0_sign c2_node) (normalization_3614 c0_node c0_sign c2_node))

-- Checked replay of monotonicity.
theorem replay_1329 (c0_node c0_sign c2_node : Int) : ((formula_962 c0_node c0_sign c2_node) ↔ (formula_980 c0_node c0_sign c2_node)) := by
  classical
  have ht := (normalized_801 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Classification027_35 c0_node c2_node) := by
    exact Iff.mp (normalization_3613 c0_node c2_node) (replay_1328 c0_node c2_node)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3615 c0_node c0_sign c2_node) hn

theorem normalized_802 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_43 (c0_node c2_node : Int) : Prop := (((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3616 (c0_node c0_sign c2_node : Int) : (formula_939 c0_node c0_sign c2_node) ↔ ((shared_expr_Classification027_43 c0_node c2_node) ∨ (shared_expr_Classification027_39 c0_node c0_sign c2_node)) := (or_congr (and_congr (normalization_3610 c0_node c2_node) (normalization_3492 c0_node c2_node)) (and_congr (not_congr (normalization_3610 c0_node c2_node)) (normalization_3582 c0_sign)))

abbrev shared_expr_Classification027_44 (c0_node c0_sign c2_node : Int) : Prop := (((shared_expr_Classification027_39 c0_node c0_sign c2_node) ∨ (shared_expr_Classification027_40 c0_node c2_node)) ↔ ((shared_expr_Classification027_43 c0_node c2_node) ∨ (shared_expr_Classification027_39 c0_node c0_sign c2_node)))
theorem normalization_3617 (c0_node c0_sign c2_node : Int) : ((formula_980 c0_node c0_sign c2_node) ↔ (formula_939 c0_node c0_sign c2_node)) ↔ (shared_expr_Classification027_44 c0_node c0_sign c2_node) := (iff_congr (normalization_3614 c0_node c0_sign c2_node) (normalization_3616 c0_node c0_sign c2_node))

-- Checked replay of rewrite.
theorem replay_1330 (c0_node c0_sign c2_node : Int) : ((formula_980 c0_node c0_sign c2_node) ↔ (formula_939 c0_node c0_sign c2_node)) := by
  classical
  have ht := (normalized_802 ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3617 c0_node c0_sign c2_node) hn

theorem normalized_803 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3618 (c0_node c0_sign c2_node : Int) : ((formula_962 c0_node c0_sign c2_node) ↔ (formula_939 c0_node c0_sign c2_node)) ↔ ((shared_expr_Classification027_42 c0_node c0_sign c2_node) ↔ ((shared_expr_Classification027_43 c0_node c2_node) ∨ (shared_expr_Classification027_39 c0_node c0_sign c2_node))) := (iff_congr (normalization_3493 c0_node c0_sign c2_node) (normalization_3616 c0_node c0_sign c2_node))

-- Checked replay of trans.
theorem replay_1331 (c0_node c0_sign c2_node : Int) : ((formula_962 c0_node c0_sign c2_node) ↔ (formula_939 c0_node c0_sign c2_node)) := by
  classical
  have ht := (normalized_803 (shared_expr_Classification027_42 c0_node c0_sign c2_node) ((shared_expr_Classification027_39 c0_node c0_sign c2_node) ∨ (shared_expr_Classification027_40 c0_node c2_node)) ((shared_expr_Classification027_43 c0_node c2_node) ∨ (shared_expr_Classification027_39 c0_node c0_sign c2_node)))
  have n0 : ((shared_expr_Classification027_42 c0_node c0_sign c2_node) ↔ ((shared_expr_Classification027_39 c0_node c0_sign c2_node) ∨ (shared_expr_Classification027_40 c0_node c2_node))) := by
    exact Iff.mp (normalization_3615 c0_node c0_sign c2_node) (replay_1329 c0_node c0_sign c2_node)
  have n1 : (shared_expr_Classification027_44 c0_node c0_sign c2_node) := by
    exact Iff.mp (normalization_3617 c0_node c0_sign c2_node) (replay_1330 c0_node c0_sign c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3618 c0_node c0_sign c2_node) hn

theorem normalized_804 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3619 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_3620 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_3621 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := (and_congr (normalization_3619 c0_depth c2_depth) (normalization_3620 c0_depth c2_depth))

abbrev shared_expr_Classification027_45 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))
theorem normalization_3622 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification027_45 c0_depth c2_depth) := (iff_congr (normalization_3494 c0_depth c2_depth) (normalization_3621 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1332 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_804 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3622 c0_depth c2_depth) hn

abbrev shared_expr_Classification027_46 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))
abbrev formula_981 (c0_depth c2_depth : Int) : Prop := (shared_expr_Classification027_46 c0_depth c2_depth)

theorem normalized_805 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3623 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) := (not_congr (normalization_3619 c0_depth c2_depth))

theorem normalization_3624 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := (not_congr (normalization_3620 c0_depth c2_depth))

theorem normalization_3625 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) := (or_congr (normalization_3623 c0_depth c2_depth) (normalization_3624 c0_depth c2_depth))

theorem normalization_3626 (c0_depth c2_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_3625 c0_depth c2_depth))

abbrev shared_expr_Classification027_47 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))))))
theorem normalization_3627 (c0_depth c2_depth : Int) : (formula_981 c0_depth c2_depth) ↔ (shared_expr_Classification027_47 c0_depth c2_depth) := (iff_congr (normalization_3621 c0_depth c2_depth) (normalization_3626 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1333 (c0_depth c2_depth : Int) : (formula_981 c0_depth c2_depth) := by
  classical
  have ht := (normalized_805 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3627 c0_depth c2_depth) hn

theorem normalized_806 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3628 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification027_47 c0_depth c2_depth) := (iff_congr (normalization_3494 c0_depth c2_depth) (normalization_3626 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_1334 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_806 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (shared_expr_Classification027_47 c0_depth c2_depth))
  have n0 : (shared_expr_Classification027_45 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3622 c0_depth c2_depth) (replay_1332 c0_depth c2_depth)
  have n1 : (shared_expr_Classification027_47 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3627 c0_depth c2_depth) (replay_1333 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3628 c0_depth c2_depth) hn

theorem normalized_807 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3629 (c0_depth c2_depth : Int) : (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_3626 c0_depth c2_depth))

abbrev shared_expr_Classification027_48 (c0_depth c2_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))))
theorem normalization_3630 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Classification027_48 c0_depth c2_depth) := (iff_congr (normalization_3495 c0_depth c2_depth) (normalization_3629 c0_depth c2_depth))

-- Checked replay of monotonicity.
theorem replay_1335 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_807 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification027_47 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3628 c0_depth c2_depth) (replay_1334 c0_depth c2_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_3630 c0_depth c2_depth) hn

abbrev shared_expr_Classification027_49 (c0_depth c2_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))))
abbrev formula_982 (c0_depth c2_depth : Int) : Prop := (shared_expr_Classification027_49 c0_depth c2_depth)

theorem normalized_808 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_50 (c0_depth c2_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
theorem normalization_3631 (c0_depth c2_depth : Int) : (formula_982 c0_depth c2_depth) ↔ (shared_expr_Classification027_50 c0_depth c2_depth) := (iff_congr (normalization_3629 c0_depth c2_depth) (normalization_3625 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_1336 (c0_depth c2_depth : Int) : (formula_982 c0_depth c2_depth) := by
  classical
  have ht := (normalized_808 ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_3631 c0_depth c2_depth) hn

theorem normalized_809 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification027_51 (c0_depth c2_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
theorem normalization_3632 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Classification027_51 c0_depth c2_depth) := (iff_congr (normalization_3495 c0_depth c2_depth) (normalization_3625 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_1337 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_809 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification027_48 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3630 c0_depth c2_depth) (replay_1335 c0_depth c2_depth)
  have n1 : (shared_expr_Classification027_50 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3631 c0_depth c2_depth) (replay_1336 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3632 c0_depth c2_depth) hn

end H4Formal.Generated.Classification
