import H4Formal.Certificates.CheckedClassification.Classification051

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_1427 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6046 (r1_sign : Int) : ((r1_sign ≤ (0 : Int)) ∧ (r1_sign ≥ (0 : Int))) ↔ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) := (and_congr (normalization_74 r1_sign) (normalization_72 r1_sign))

theorem normalization_6047 (r1_sign : Int) : ((r1_sign = (0 : Int)) ↔ ((r1_sign ≤ (0 : Int)) ∧ (r1_sign ≥ (0 : Int)))) ↔ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_10 r1_sign) (normalization_6046 r1_sign))

-- Checked replay of rewrite.
theorem replay_2708 (r1_sign : Int) : ((r1_sign = (0 : Int)) ↔ ((r1_sign ≤ (0 : Int)) ∧ (r1_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1427 (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6047 r1_sign) hn

theorem normalized_1428 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6048 (r1_sign : Int) : (((r1_sign ≤ (0 : Int)) ∧ (r1_sign ≥ (0 : Int))) ↔ (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))))) ↔ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_6046 r1_sign) (normalization_113 r1_sign))

-- Checked replay of rewrite.
theorem replay_2709 (r1_sign : Int) : (((r1_sign ≤ (0 : Int)) ∧ (r1_sign ≥ (0 : Int))) ↔ (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1428 ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6048 r1_sign) hn

theorem normalized_1429 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6049 (r1_sign : Int) : ((r1_sign = (0 : Int)) ↔ (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))))) ↔ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_10 r1_sign) (normalization_113 r1_sign))

-- Checked replay of trans.
theorem replay_2710 (r1_sign : Int) : ((r1_sign = (0 : Int)) ↔ (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1429 (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))))))
  have n0 : ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_6047 r1_sign) (replay_2708 r1_sign)
  have n1 : ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6048 r1_sign) (replay_2709 r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6049 r1_sign) hn

abbrev shared_expr_Classification052_0 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((r1_sign = (0 : Int)) ∧ (c0_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev formula_1747 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_0 c0_node c0_sign r1_node r1_sign)

theorem normalized_1430 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6050 (c0_node c0_sign r1_node r1_sign : Int) : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_113 r1_sign) (and_congr (normalization_3582 c0_sign) (normalization_5878 c0_node r1_node)))

abbrev shared_expr_Classification052_1 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ↔ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
theorem normalization_6051 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1747 c0_node c0_sign r1_node r1_sign) ↔ (shared_expr_Classification052_1 c0_node c0_sign r1_node r1_sign) := (iff_congr (normalization_5879 c0_node c0_sign r1_node r1_sign) (normalization_6050 c0_node c0_sign r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2711 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1747 c0_node c0_sign r1_node r1_sign) := by
  classical
  have ht := (normalized_1430 (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have n0 : ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6049 r1_sign) (replay_2710 r1_sign)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6051 c0_node c0_sign r1_node r1_sign) hn

abbrev shared_expr_Classification052_2 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
abbrev formula_1748 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_2 c0_node c0_sign r1_node r1_sign)

theorem normalized_1431 (p0 p1 p2 p3 p4 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4)) ↔ (¬ ((¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6052 (c0_node r1_node : Int) : (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5878 c0_node r1_node))

theorem normalization_6053 (c0_node c0_sign r1_node r1_sign : Int) : ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ↔ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) := (or_congr (normalization_73 r1_sign) (or_congr (normalization_75 r1_sign) (or_congr (normalization_3579 c0_sign) (or_congr (normalization_3580 c0_sign) (normalization_6052 c0_node r1_node)))))

theorem normalization_6054 (c0_node c0_sign r1_node r1_sign : Int) : (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_6053 c0_node c0_sign r1_node r1_sign))

abbrev shared_expr_Classification052_3 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))))
theorem normalization_6055 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1748 c0_node c0_sign r1_node r1_sign) ↔ (shared_expr_Classification052_3 c0_node c0_sign r1_node r1_sign) := (iff_congr (normalization_6050 c0_node c0_sign r1_node r1_sign) (normalization_6054 c0_node c0_sign r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2712 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1748 c0_node c0_sign r1_node r1_sign) := by
  classical
  have ht := (normalized_1431 ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6055 c0_node c0_sign r1_node r1_sign) hn

abbrev shared_expr_Classification052_4 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((r1_sign = (0 : Int)) ∧ (c0_sign = (0 : Int)) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
abbrev formula_1749 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_4 c0_node c0_sign r1_node r1_sign)

theorem normalized_1432 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_5 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))))
theorem normalization_6056 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1749 c0_node c0_sign r1_node r1_sign) ↔ (shared_expr_Classification052_5 c0_node c0_sign r1_node r1_sign) := (iff_congr (normalization_5879 c0_node c0_sign r1_node r1_sign) (normalization_6054 c0_node c0_sign r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2713 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1749 c0_node c0_sign r1_node r1_sign) := by
  classical
  have ht := (normalized_1432 ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))))
  have n0 : (shared_expr_Classification052_1 c0_node c0_sign r1_node r1_sign) := by
    exact Iff.mp (normalization_6051 c0_node c0_sign r1_node r1_sign) (replay_2711 c0_node c0_sign r1_node r1_sign)
  have n1 : (shared_expr_Classification052_3 c0_node c0_sign r1_node r1_sign) := by
    exact Iff.mp (normalization_6055 c0_node c0_sign r1_node r1_sign) (replay_2712 c0_node c0_sign r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6056 c0_node c0_sign r1_node r1_sign) hn

theorem normalized_1433 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6057 (r1_sign : Int) : ((r1_sign ≤ (2 : Int)) ∧ (r1_sign ≥ (2 : Int))) ↔ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) := (and_congr (normalization_121 r1_sign) (normalization_123 r1_sign))

theorem normalization_6058 (r1_sign : Int) : ((r1_sign = (2 : Int)) ↔ ((r1_sign ≤ (2 : Int)) ∧ (r1_sign ≥ (2 : Int)))) ↔ ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) := (iff_congr (normalization_25 r1_sign) (normalization_6057 r1_sign))

-- Checked replay of rewrite.
theorem replay_2714 (r1_sign : Int) : ((r1_sign = (2 : Int)) ↔ ((r1_sign ≤ (2 : Int)) ∧ (r1_sign ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_1433 (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6058 r1_sign) hn

theorem normalized_1434 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6059 (r1_sign : Int) : (((r1_sign ≤ (2 : Int)) ∧ (r1_sign ≥ (2 : Int))) ↔ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ↔ ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_6057 r1_sign) (normalization_126 r1_sign))

-- Checked replay of rewrite.
theorem replay_2715 (r1_sign : Int) : (((r1_sign ≤ (2 : Int)) ∧ (r1_sign ≥ (2 : Int))) ↔ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_1434 ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6059 r1_sign) hn

theorem normalized_1435 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6060 (r1_sign : Int) : ((r1_sign = (2 : Int)) ↔ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ↔ ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))) := (iff_congr (normalization_25 r1_sign) (normalization_126 r1_sign))

-- Checked replay of trans.
theorem replay_2716 (r1_sign : Int) : ((r1_sign = (2 : Int)) ↔ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_1435 (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))))
  have n0 : ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_6058 r1_sign) (replay_2714 r1_sign)
  have n1 : ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6059 r1_sign) (replay_2715 r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6060 r1_sign) hn

theorem normalized_1436 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6061 (h r1_depth : Int) : (r1_depth ≥ h) ↔ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6062 (h r1_depth : Int) : ((r1_depth ≤ h) ∧ (r1_depth ≥ h)) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (and_congr (normalization_21 h r1_depth) (normalization_6061 h r1_depth))

theorem normalization_6063 (h r1_depth : Int) : ((r1_depth = h) ↔ ((r1_depth ≤ h) ∧ (r1_depth ≥ h))) ↔ (((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := (iff_congr (normalization_24 h r1_depth) (normalization_6062 h r1_depth))

-- Checked replay of rewrite.
theorem replay_2717 (h r1_depth : Int) : ((r1_depth = h) ↔ ((r1_depth ≤ h) ∧ (r1_depth ≥ h))) := by
  classical
  have ht := (normalized_1436 ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6063 h r1_depth) hn

theorem normalized_1437 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6064 (h r1_depth : Int) : ((r1_depth ≤ h) ↔ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_21 h r1_depth) (normalization_47 h r1_depth))

-- Checked replay of rewrite.
theorem replay_2718 (h r1_depth : Int) : ((r1_depth ≤ h) ↔ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1437 ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6064 h r1_depth) hn

theorem normalized_1438 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6065 (h r1_depth : Int) : ((r1_depth ≥ h) ↔ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (iff_congr (normalization_6061 h r1_depth) (normalization_109 h r1_depth))

-- Checked replay of rewrite.
theorem replay_2719 (h r1_depth : Int) : ((r1_depth ≥ h) ↔ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1438 ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6065 h r1_depth) hn

theorem normalized_1439 (p0 p1 p2 : Prop) : ((((¬ p0) ↔ (¬ p0)) ∧ (p1 ↔ p1)) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6066 (h r1_depth : Int) : (((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (and_congr (normalization_47 h r1_depth) (normalization_109 h r1_depth))

theorem normalization_6067 (h r1_depth : Int) : (((r1_depth ≤ h) ∧ (r1_depth ≥ h)) ↔ (((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) ↔ (((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := (iff_congr (normalization_6062 h r1_depth) (normalization_6066 h r1_depth))

-- Checked replay of monotonicity.
theorem replay_2720 (h r1_depth : Int) : (((r1_depth ≤ h) ∧ (r1_depth ≥ h)) ↔ (((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := by
  classical
  have ht := (normalized_1439 ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
  have n0 : ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_6064 h r1_depth) (replay_2718 h r1_depth)
  have n1 : (((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_6065 h r1_depth) (replay_2719 h r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6067 h r1_depth) hn

theorem normalized_1440 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ p1) ∨ (¬ (¬ p0))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6068 (h r1_depth : Int) : (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_111 h r1_depth))

abbrev shared_expr_Classification052_6 (h r1_depth : Int) : Prop := (((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))))))
theorem normalization_6069 (h r1_depth : Int) : ((((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification052_6 h r1_depth) := (iff_congr (normalization_6066 h r1_depth) (normalization_6068 h r1_depth))

-- Checked replay of rewrite.
theorem replay_2721 (h r1_depth : Int) : ((((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1440 ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6069 h r1_depth) hn

theorem normalized_1441 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6070 (h r1_depth : Int) : (((r1_depth ≤ h) ∧ (r1_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification052_6 h r1_depth) := (iff_congr (normalization_6062 h r1_depth) (normalization_6068 h r1_depth))

-- Checked replay of trans.
theorem replay_2722 (h r1_depth : Int) : (((r1_depth ≤ h) ∧ (r1_depth ≥ h)) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1441 ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (shared_expr_Classification052_6 h r1_depth))
  have n0 : (((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := by
    exact Iff.mp (normalization_6067 h r1_depth) (replay_2720 h r1_depth)
  have n1 : (shared_expr_Classification052_6 h r1_depth) := by
    exact Iff.mp (normalization_6069 h r1_depth) (replay_2721 h r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6070 h r1_depth) hn

theorem normalized_1442 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6071 (h r1_depth : Int) : ((r1_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification052_6 h r1_depth) := (iff_congr (normalization_24 h r1_depth) (normalization_6068 h r1_depth))

-- Checked replay of trans.
theorem replay_2723 (h r1_depth : Int) : ((r1_depth = h) ↔ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1442 ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (shared_expr_Classification052_6 h r1_depth))
  have n0 : (((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := by
    exact Iff.mp (normalization_6063 h r1_depth) (replay_2717 h r1_depth)
  have n1 : (shared_expr_Classification052_6 h r1_depth) := by
    exact Iff.mp (normalization_6070 h r1_depth) (replay_2722 h r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6071 h r1_depth) hn

abbrev shared_expr_Classification052_7 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))))) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
abbrev formula_1750 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_7 c0_node c0_sign h r1_depth r1_node r1_sign)

theorem normalized_1443 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∧ p2 ∧ p4 ∧ (¬ p6)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p5) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_8 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
theorem normalization_6072 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1750 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_8 c0_node c0_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_126 r1_sign) (and_congr (normalization_5233 c0_sign) (and_congr (normalization_6068 h r1_depth) (normalization_5878 c0_node r1_node))))

abbrev shared_expr_Classification052_9 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ∧ (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
theorem normalization_6073 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c0_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (formula_1750 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification052_9 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_8 c0_node c0_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_5880 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6072 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2724 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c0_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (formula_1750 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1443 (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))) (((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))) ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))) ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have n0 : ((((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_6060 r1_sign) (replay_2716 r1_sign)
  have n1 : ((((c0_sign) ≤ (2 : Int)) ∧ (¬ ((c0_sign) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_5569 c0_sign) (replay_2615 c0_sign)
  have n2 : (shared_expr_Classification052_6 h r1_depth) := by
    exact Iff.mp (normalization_6071 h r1_depth) (replay_2723 h r1_depth)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6073 c0_node c0_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1444 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ ((¬ p4) ∨ (¬ (¬ p5)))) ∧ (¬ p6)) ↔ (¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p6))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_10 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))) ∨ (¬ ((c0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
theorem normalization_6074 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1649 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_110 h r1_depth) (or_congr (normalization_104 h r1_depth) (or_congr (normalization_122 r1_sign) (or_congr (normalization_124 r1_sign) (or_congr (normalization_5229 c0_sign) (or_congr (normalization_5231 c0_sign) (normalization_6052 c0_node r1_node)))))))

theorem normalization_6075 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (¬ (formula_1649 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign)) := (not_congr (normalization_6074 c0_node c0_sign h r1_depth r1_node r1_sign))

theorem normalization_6076 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1750 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_1649 c0_node c0_sign h r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification052_8 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_6072 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6075 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2725 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1750 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_1649 c0_node c0_sign h r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1444 ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)) ((c0_sign) ≤ (2 : Int)) ((c0_sign) ≤ (1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6076 c0_node c0_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1445 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6077 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c0_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ (formula_1649 c0_node c0_sign h r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification052_9 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_5880 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6075 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2726 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (((r1_sign = (2 : Int)) ∧ (c0_sign = (2 : Int)) ∧ (r1_depth = h) ∧ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ (formula_1649 c0_node c0_sign h r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1445 (shared_expr_Classification052_9 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_8 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign))
  have n0 : ((shared_expr_Classification052_9 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_8 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6073 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2724 c0_node c0_sign h r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification052_8 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6076 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2725 c0_node c0_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6077 c0_node c0_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1446 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6078 (r1_sign : Int) : ((r1_sign ≤ (1 : Int)) ∧ (r1_sign ≥ (1 : Int))) ↔ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) := (and_congr (normalization_114 r1_sign) (normalization_116 r1_sign))

theorem normalization_6079 (r1_sign : Int) : ((r1_sign = (1 : Int)) ↔ ((r1_sign ≤ (1 : Int)) ∧ (r1_sign ≥ (1 : Int)))) ↔ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int))))) := (iff_congr (normalization_26 r1_sign) (normalization_6078 r1_sign))

-- Checked replay of rewrite.
theorem replay_2727 (r1_sign : Int) : ((r1_sign = (1 : Int)) ↔ ((r1_sign ≤ (1 : Int)) ∧ (r1_sign ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1446 (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6079 r1_sign) hn

theorem normalized_1447 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6080 (r1_sign : Int) : (((r1_sign ≤ (1 : Int)) ∧ (r1_sign ≥ (1 : Int))) ↔ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))) ↔ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_6078 r1_sign) (normalization_119 r1_sign))

-- Checked replay of rewrite.
theorem replay_2728 (r1_sign : Int) : (((r1_sign ≤ (1 : Int)) ∧ (r1_sign ≥ (1 : Int))) ↔ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1447 ((r1_sign) ≤ (1 : Int)) ((r1_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6080 r1_sign) hn

theorem normalized_1448 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6081 (r1_sign : Int) : ((r1_sign = (1 : Int)) ↔ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))) ↔ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_26 r1_sign) (normalization_119 r1_sign))

-- Checked replay of trans.
theorem replay_2729 (r1_sign : Int) : ((r1_sign = (1 : Int)) ↔ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1448 (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))))
  have n0 : ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_6079 r1_sign) (replay_2727 r1_sign)
  have n1 : ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6080 r1_sign) (replay_2728 r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6081 r1_sign) hn

abbrev shared_expr_Classification052_11 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int))))
abbrev formula_1751 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_11 c0_node c0_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Classification052_12 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_sign = (1 : Int)) ∧ (c0_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)))) ↔ (formula_1751 c0_node c0_sign h r1_depth r1_node r1_sign))
abbrev formula_1752 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_12 c0_node c0_sign h r1_depth r1_node r1_sign)

theorem normalized_1449 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2 ∧ (¬ p4) ∧ (¬ p5)) ↔ ((¬ p1) ∧ (¬ p3) ∧ (¬ p4) ∧ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_13 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
theorem normalization_6082 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1751 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_13 c0_node c0_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_119 r1_sign) (and_congr (normalization_5226 c0_sign) (and_congr (normalization_110 h r1_depth) (normalization_5882 c0_node r1_node))))

abbrev shared_expr_Classification052_14 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
theorem normalization_6083 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1752 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ ((shared_expr_Classification052_14 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_13 c0_node c0_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_5883 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6082 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2730 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1752 c0_node c0_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1449 (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))) (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int))))) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)))
  have n0 : ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_6081 r1_sign) (replay_2729 r1_sign)
  have n1 : ((((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_5579 c0_sign) (replay_2621 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6083 c0_node c0_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1450 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ (¬ p4) ∧ (¬ p5)) ↔ (¬ (p4 ∨ p5 ∨ (¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_15 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∨ ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∨ (¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))))
theorem normalization_6084 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1650 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_109 h r1_depth) (or_congr (normalization_5881 c0_node r1_node) (or_congr (normalization_115 r1_sign) (or_congr (normalization_117 r1_sign) (or_congr (normalization_5222 c0_sign) (normalization_5224 c0_sign))))))

theorem normalization_6085 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (¬ (formula_1650 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign)) := (not_congr (normalization_6084 c0_node c0_sign h r1_depth r1_node r1_sign))

theorem normalization_6086 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1751 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_1650 c0_node c0_sign h r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification052_13 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_6082 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6085 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2731 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1751 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (formula_1650 c0_node c0_sign h r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1450 ((r1_sign) ≤ (1 : Int)) ((r1_sign) ≤ (0 : Int)) ((c0_sign) ≤ (1 : Int)) ((c0_sign) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6086 c0_node c0_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification052_16 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_sign = (1 : Int)) ∧ (c0_sign = (1 : Int)) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)))) ↔ (¬ (formula_1650 c0_node c0_sign h r1_depth r1_node r1_sign)))
abbrev formula_1753 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_16 c0_node c0_sign h r1_depth r1_node r1_sign)

theorem normalized_1451 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6087 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1753 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ ((shared_expr_Classification052_14 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_5883 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6085 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2732 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1753 c0_node c0_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1451 (shared_expr_Classification052_14 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_13 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign))
  have n0 : ((shared_expr_Classification052_14 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_13 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6083 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2730 c0_node c0_sign h r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification052_13 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6086 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2731 c0_node c0_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6087 c0_node c0_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification052_17 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∨ (¬ (formula_1649 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_1650 c0_node c0_sign h r1_depth r1_node r1_sign)))
abbrev formula_1754 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_17 c0_node c0_sign h r1_depth r1_node r1_sign)

theorem normalized_1452 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → ((p0 ∨ p2 ∨ p4) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_18 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign)))
theorem normalization_6088 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1754 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_18 c0_node c0_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_6054 c0_node c0_sign r1_node r1_sign) (or_congr (normalization_6075 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6085 c0_node c0_sign h r1_depth r1_node r1_sign)))

abbrev shared_expr_Classification052_19 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Classification052_9 c0_node c0_sign h r1_depth r1_node r1_sign) ∨ (shared_expr_Classification052_14 c0_node c0_sign h r1_depth r1_node r1_sign))
theorem normalization_6089 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1731 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (formula_1754 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_18 c0_node c0_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_5884 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6088 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2733 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1731 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (formula_1754 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1452 ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) (shared_expr_Classification052_9 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_14 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign))
  have n0 : (shared_expr_Classification052_5 c0_node c0_sign r1_node r1_sign) := by
    exact Iff.mp (normalization_6056 c0_node c0_sign r1_node r1_sign) (replay_2713 c0_node c0_sign r1_node r1_sign)
  have n1 : ((shared_expr_Classification052_9 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6077 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2726 c0_node c0_sign h r1_depth r1_node r1_sign)
  have n2 : ((shared_expr_Classification052_14 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6087 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2732 c0_node c0_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6089 c0_node c0_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1453 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ↔ ((¬ p1) ∨ (¬ p0) ∨ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_20 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign)))
theorem normalization_6090 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_6075 c0_node c0_sign h r1_depth r1_node r1_sign) (or_congr (normalization_6054 c0_node c0_sign r1_node r1_sign) (normalization_6085 c0_node c0_sign h r1_depth r1_node r1_sign)))

theorem normalization_6091 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1754 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification052_18 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_6088 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6090 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2734 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1754 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1453 ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) (shared_expr_Classification052_10 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_15 c0_node c0_sign h r1_depth r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_6091 c0_node c0_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1454 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6092 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1731 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign)) := (iff_congr (normalization_5884 c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6090 c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2735 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_1731 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1454 (shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_18 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign))
  have n0 : ((shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_18 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6089 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2733 c0_node c0_sign h r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification052_18 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6091 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2734 c0_node c0_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6092 c0_node c0_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification052_21 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_depth = c0_depth) ∧ (formula_1731 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ ((¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))))) ∧ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)))
abbrev formula_1755 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_21 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)

theorem normalized_1455 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_22 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))) ∧ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign))
theorem normalization_6093 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))))) ∧ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (shared_expr_Classification052_22 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := (and_congr (normalization_6042 c0_depth r1_depth) (normalization_6090 c0_node c0_sign h r1_depth r1_node r1_sign))

abbrev shared_expr_Classification052_23 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (shared_expr_Classification052_22 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))
theorem normalization_6094 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1755 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_23 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := (iff_congr (normalization_5885 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6093 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification052_24 (c0_depth r1_depth : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))))
theorem replay_2736 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1755 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1455 ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign))
  have n0 : (shared_expr_Classification052_24 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6045 c0_depth r1_depth) (replay_2707 c0_depth r1_depth)
  have n1 : ((shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6092 c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2735 c0_node c0_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6094 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification052_25 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))))) ∧ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)))))
abbrev formula_1756 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_25 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)

theorem normalized_1456 (p0 p1 p2 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ p2) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6095 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (¬ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign)) := (not_congr (normalization_6090 c0_node c0_sign h r1_depth r1_node r1_sign))

abbrev shared_expr_Classification052_26 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign)))
theorem normalization_6096 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign))) ↔ (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := (or_congr (normalization_6039 c0_depth r1_depth) (or_congr (normalization_6040 c0_depth r1_depth) (normalization_6095 c0_node c0_sign h r1_depth r1_node r1_sign)))

theorem normalization_6097 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)))) ↔ (¬ (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) := (not_congr (normalization_6096 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))

theorem normalization_6098 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1756 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) ↔ ((shared_expr_Classification052_22 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))) := (iff_congr (normalization_6093 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6097 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2737 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1756 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1456 ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) (shared_expr_Classification052_20 c0_node c0_sign h r1_depth r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_6098 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) hn

abbrev shared_expr_Classification052_27 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((r1_depth = c0_depth) ∧ (formula_1731 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1651 c0_node c0_sign h r1_depth r1_node r1_sign)))))
abbrev formula_1757 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_27 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)

theorem normalized_1457 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_28 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)))
theorem normalization_6099 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1757 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_28 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := (iff_congr (normalization_5885 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6097 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2738 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_1757 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
  classical
  have ht := (normalized_1457 (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign)) (shared_expr_Classification052_22 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))
  have n0 : (shared_expr_Classification052_23 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
    exact Iff.mp (normalization_6094 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2736 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification052_22 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6098 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2737 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6099 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) hn

theorem normalized_1458 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6100 (c0_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_6101 (c0_depth r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6102 (c0_depth r1_depth : Int) : (((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := (and_congr (normalization_6100 c0_depth r1_depth) (normalization_6101 c0_depth r1_depth))

abbrev shared_expr_Classification052_29 (c0_depth r1_depth : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))
theorem normalization_6103 (c0_depth r1_depth : Int) : (((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification052_29 c0_depth r1_depth) := (iff_congr (normalization_5886 c0_depth r1_depth) (normalization_6102 c0_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_2739 (c0_depth r1_depth : Int) : (((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1458 ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_6103 c0_depth r1_depth) hn

abbrev shared_expr_Classification052_30 (c0_depth r1_depth : Int) : Prop := ((((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ∧ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))))
abbrev formula_1758 (c0_depth r1_depth : Int) : Prop := (shared_expr_Classification052_30 c0_depth r1_depth)

theorem normalized_1459 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6104 (c0_depth r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_6100 c0_depth r1_depth))

theorem normalization_6105 (c0_depth r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := (not_congr (normalization_6101 c0_depth r1_depth))

theorem normalization_6106 (c0_depth r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))) ↔ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (or_congr (normalization_6104 c0_depth r1_depth) (normalization_6105 c0_depth r1_depth))

theorem normalization_6107 (c0_depth r1_depth : Int) : (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) := (not_congr (normalization_6106 c0_depth r1_depth))

abbrev shared_expr_Classification052_31 (c0_depth r1_depth : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ↔ (¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))))
theorem normalization_6108 (c0_depth r1_depth : Int) : (formula_1758 c0_depth r1_depth) ↔ (shared_expr_Classification052_31 c0_depth r1_depth) := (iff_congr (normalization_6102 c0_depth r1_depth) (normalization_6107 c0_depth r1_depth))

-- Checked replay of rewrite.
theorem replay_2740 (c0_depth r1_depth : Int) : (formula_1758 c0_depth r1_depth) := by
  classical
  have ht := (normalized_1459 ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6108 c0_depth r1_depth) hn

theorem normalized_1460 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6109 (c0_depth r1_depth : Int) : (((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification052_31 c0_depth r1_depth) := (iff_congr (normalization_5886 c0_depth r1_depth) (normalization_6107 c0_depth r1_depth))

-- Checked replay of trans.
theorem replay_2741 (c0_depth r1_depth : Int) : (((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1460 ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) (shared_expr_Classification052_31 c0_depth r1_depth))
  have n0 : (shared_expr_Classification052_29 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6103 c0_depth r1_depth) (replay_2739 c0_depth r1_depth)
  have n1 : (shared_expr_Classification052_31 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6108 c0_depth r1_depth) (replay_2740 c0_depth r1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6109 c0_depth r1_depth) hn

theorem normalized_1461 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ∧ (p4 ∧ (¬ p5)) ∧ p6) ∨ (((p3 ∧ (¬ p0)) ∨ (p2 ∧ (¬ p3))) ∧ (p7 ∧ (¬ p4)) ∧ (¬ (¬ p8)))) ↔ ((¬ ((¬ p4) ∨ (¬ (¬ p5)) ∨ (¬ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) ∨ (¬ p6))) ∨ (¬ ((¬ p8) ∨ (¬ p7) ∨ (¬ (¬ p4)) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ (¬ p0)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6110 (r1_sign : Int) : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))) := (or_congr (normalization_113 r1_sign) (normalization_126 r1_sign))

theorem normalization_6111 (r1_sign : Int) : (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_6110 r1_sign))

theorem normalization_6112 (c0_node r1_node : Int) : (¬ ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (not_congr (normalization_5887 c0_node r1_node))

abbrev shared_expr_Classification052_32 (c0_node c0_sign r1_node r1_sign : Int) : Prop := ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) ∨ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_6113 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1652 c0_node c0_sign r1_node r1_sign) ↔ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign) := (or_congr (normalization_3579 c0_sign) (or_congr (normalization_3580 c0_sign) (or_congr (normalization_6111 r1_sign) (normalization_6112 c0_node r1_node))))

theorem normalization_6114 (c0_node c0_sign r1_node r1_sign : Int) : (¬ (formula_1652 c0_node c0_sign r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) := (not_congr (normalization_6113 c0_node c0_sign r1_node r1_sign))

theorem normalization_6115 (r1_sign : Int) : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))) := (or_congr (normalization_119 r1_sign) (normalization_126 r1_sign))

theorem normalization_6116 (r1_sign : Int) : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_6115 r1_sign))

abbrev shared_expr_Classification052_33 (c0_node c0_sign r1_node r1_sign : Int) : Prop := ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∨ (¬ ((c0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))))
theorem normalization_6117 (c0_node c0_sign r1_node r1_sign : Int) : (formula_1653 c0_node c0_sign r1_node r1_sign) ↔ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign) := (or_congr (normalization_5889 c0_node r1_node) (or_congr (normalization_5222 c0_sign) (or_congr (normalization_5224 c0_sign) (normalization_6116 r1_sign))))

theorem normalization_6118 (c0_node c0_sign r1_node r1_sign : Int) : (¬ (formula_1653 c0_node c0_sign r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign)) := (not_congr (normalization_6117 c0_node c0_sign r1_node r1_sign))

theorem normalization_6119 (c0_node c0_sign r1_node r1_sign : Int) : ((¬ (formula_1652 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (formula_1653 c0_node c0_sign r1_node r1_sign))) ↔ ((¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign))) := (or_congr (normalization_6114 c0_node c0_sign r1_node r1_sign) (normalization_6118 c0_node c0_sign r1_node r1_sign))

abbrev shared_expr_Classification052_34 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
abbrev shared_expr_Classification052_35 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ (((c0_sign) ≤ (1 : Int)) ∧ (¬ ((c0_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification052_36 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((shared_expr_Classification052_34 c0_node c0_sign r1_node r1_sign) ∨ (shared_expr_Classification052_35 c0_node c0_sign r1_node r1_sign)) ↔ ((¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign))))
theorem normalization_6120 (c0_node c0_sign r1_node r1_sign : Int) : ((formula_1732 c0_node c0_sign r1_node r1_sign) ↔ ((¬ (formula_1652 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (formula_1653 c0_node c0_sign r1_node r1_sign)))) ↔ (shared_expr_Classification052_36 c0_node c0_sign r1_node r1_sign) := (iff_congr (normalization_5892 c0_node c0_sign r1_node r1_sign) (normalization_6119 c0_node c0_sign r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2742 (c0_node c0_sign r1_node r1_sign : Int) : ((formula_1732 c0_node c0_sign r1_node r1_sign) ↔ ((¬ (formula_1652 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (formula_1653 c0_node c0_sign r1_node r1_sign)))) := by
  classical
  have ht := (normalized_1461 ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)) ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ((c0_sign) ≤ (1 : Int)) (((r1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6120 c0_node c0_sign r1_node r1_sign) hn

abbrev shared_expr_Classification052_37 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))) ∧ ((¬ (formula_1652 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (formula_1653 c0_node c0_sign r1_node r1_sign))))
abbrev formula_1759 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_37 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)

theorem normalized_1462 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_38 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ∧ ((¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign))))
theorem normalization_6121 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : (formula_1759 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_38 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) := (and_congr (normalization_6107 c0_depth r1_depth) (normalization_6119 c0_node c0_sign r1_node r1_sign))

abbrev shared_expr_Classification052_39 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Classification052_34 c0_node c0_sign r1_node r1_sign) ∨ (shared_expr_Classification052_35 c0_node c0_sign r1_node r1_sign)))
theorem normalization_6122 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : ((((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ (formula_1732 c0_node c0_sign r1_node r1_sign)) ↔ (formula_1759 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)) ↔ ((shared_expr_Classification052_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_38 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)) := (iff_congr (normalization_5893 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (normalization_6121 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2743 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : ((((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ (formula_1732 c0_node c0_sign r1_node r1_sign)) ↔ (formula_1759 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)) := by
  classical
  have ht := (normalized_1462 ((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ((shared_expr_Classification052_34 c0_node c0_sign r1_node r1_sign) ∨ (shared_expr_Classification052_35 c0_node c0_sign r1_node r1_sign)) ((¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign))))
  have n0 : (shared_expr_Classification052_31 c0_depth r1_depth) := by
    exact Iff.mp (normalization_6109 c0_depth r1_depth) (replay_2741 c0_depth r1_depth)
  have n1 : (shared_expr_Classification052_36 c0_node c0_sign r1_node r1_sign) := by
    exact Iff.mp (normalization_6120 c0_node c0_sign r1_node r1_sign) (replay_2742 c0_node c0_sign r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6122 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) hn

theorem normalized_1463 (p0 p1 p2 : Prop) : (((¬ ((¬ (¬ p0)) ∨ (¬ p1))) ∧ p2) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6123 (c0_node c0_sign r1_node r1_sign : Int) : (¬ ((¬ (formula_1652 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (formula_1653 c0_node c0_sign r1_node r1_sign)))) ↔ (¬ ((¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign)))) := (not_congr (normalization_6119 c0_node c0_sign r1_node r1_sign))

abbrev shared_expr_Classification052_40 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : Prop := ((¬ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∨ (¬ ((¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign)))))
theorem normalization_6124 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : (formula_1654 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) := (or_congr (normalization_6104 c0_depth r1_depth) (or_congr (normalization_6105 c0_depth r1_depth) (normalization_6123 c0_node c0_sign r1_node r1_sign)))

theorem normalization_6125 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : (¬ (formula_1654 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)) := (not_congr (normalization_6124 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))

theorem normalization_6126 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : ((formula_1759 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (¬ (formula_1654 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification052_38 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) := (iff_congr (normalization_6121 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (normalization_6125 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2744 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : ((formula_1759 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (¬ (formula_1654 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1463 ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)) ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((¬ (shared_expr_Classification052_32 c0_node c0_sign r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_33 c0_node c0_sign r1_node r1_sign))))
  have hn := ht
  exact Iff.mpr (normalization_6126 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) hn

theorem normalized_1464 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6127 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : ((((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ (formula_1732 c0_node c0_sign r1_node r1_sign)) ↔ (¬ (formula_1654 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) ↔ ((shared_expr_Classification052_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) := (iff_congr (normalization_5893 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (normalization_6125 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2745 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : ((((r1_depth + ((-1 : Int) * c0_depth)) = (1 : Int)) ∧ (formula_1732 c0_node c0_sign r1_node r1_sign)) ↔ (¬ (formula_1654 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) := by
  classical
  have ht := (normalized_1464 (shared_expr_Classification052_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (shared_expr_Classification052_38 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))
  have n0 : ((shared_expr_Classification052_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Classification052_38 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)) := by
    exact Iff.mp (normalization_6122 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (replay_2743 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)
  have n1 : ((shared_expr_Classification052_38 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6126 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (replay_2744 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6127 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) hn

theorem normalized_1465 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5)) ∧ (p6 ↔ (¬ p7))) → ((p0 ∨ p2 ∨ p4 ∨ p6) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5) ∨ (¬ p7)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_41 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)))
theorem normalization_6128 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_276 r1_kind) (or_congr (normalization_3540 c0_kind) (or_congr (normalization_6097 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (normalization_6125 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))))

abbrev shared_expr_Classification052_42 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∨ (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (shared_expr_Classification052_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))
abbrev shared_expr_Classification052_43 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification052_42 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
theorem normalization_6129 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : ((formula_1733 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) ↔ (shared_expr_Classification052_43 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (iff_congr (normalization_5894 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (normalization_6128 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2746 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : ((formula_1733 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) := by
  classical
  have ht := (normalized_1465 (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) (((¬ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (shared_expr_Classification052_19 c0_node c0_sign h r1_depth r1_node r1_sign)) (shared_expr_Classification052_26 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (shared_expr_Classification052_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))
  have n0 : ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_278 r1_kind) (replay_76 r1_kind)
  have n1 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3542 c0_kind) (replay_1299 c0_kind)
  have n2 : (shared_expr_Classification052_28 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
    exact Iff.mp (normalization_6099 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (replay_2738 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)
  have n3 : ((shared_expr_Classification052_39 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ↔ (¬ (shared_expr_Classification052_40 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))) := by
    exact Iff.mp (normalization_6127 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (replay_2745 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_6129 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) hn

theorem normalized_1466 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification052_44 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
theorem normalization_6130 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : ((formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) ↔ (shared_expr_Classification052_44 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (iff_congr (normalization_6128 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (normalization_6128 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2747 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : ((formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) := by
  classical
  have ht := (normalized_1466 (shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_6130 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) hn

theorem normalized_1467 (p0 p1 : Prop) : ((p0 ∧ (p1 ↔ p1)) → p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of trans.
theorem replay_2748 (c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : ((formula_1733 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)) := by
  classical
  have ht := (normalized_1467 (shared_expr_Classification052_43 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
  have n0 : (shared_expr_Classification052_43 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := by
    exact Iff.mp (normalization_6129 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (replay_2746 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)
  have n1 : (shared_expr_Classification052_44 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := by
    exact Iff.mp (normalization_6130 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (replay_2747 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6129 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) hn

abbrev shared_expr_Classification052_45 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) ∧ (formula_1655 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_1760 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Classification052_46 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((formula_1734 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (formula_1760 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
abbrev formula_1761 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification052_46 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)

theorem normalized_1468 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6131 (c0_level r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_6132 (c0_level r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := (not_congr (normalization_6131 c0_level r1_depth))

theorem normalization_6133 (c0_level r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_6134 (c0_level r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) := (not_congr (normalization_6133 c0_level r1_depth))

abbrev shared_expr_Classification052_47 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))))
theorem normalization_6135 (c0_level r1_depth r1_kind r1_sign : Int) : (formula_120 c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification052_47 c0_level r1_depth r1_kind r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6132 c0_level r1_depth) (or_congr (normalization_6134 c0_level r1_depth) (normalization_6111 r1_sign)))))

theorem normalization_6136 (c0_level r1_depth r1_kind r1_sign : Int) : (¬ (formula_120 c0_level r1_depth r1_kind r1_sign)) ↔ (¬ (shared_expr_Classification052_47 c0_level r1_depth r1_kind r1_sign)) := (not_congr (normalization_6135 c0_level r1_depth r1_kind r1_sign))

theorem normalization_6137 (c0_level r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6138 (c0_level r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_6137 c0_level r1_depth))

theorem normalization_6139 (c0_level r1_depth : Int) : ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_6140 (c0_level r1_depth : Int) : (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (not_congr (normalization_6139 c0_level r1_depth))

abbrev shared_expr_Classification052_48 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
theorem normalization_6141 (c0_level r1_depth r1_kind r1_sign : Int) : (formula_121 c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification052_48 c0_level r1_depth r1_kind r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6111 r1_sign) (or_congr (normalization_6138 c0_level r1_depth) (normalization_6140 c0_level r1_depth)))))

theorem normalization_6142 (c0_level r1_depth r1_kind r1_sign : Int) : (¬ (formula_121 c0_level r1_depth r1_kind r1_sign)) ↔ (¬ (shared_expr_Classification052_48 c0_level r1_depth r1_kind r1_sign)) := (not_congr (normalization_6141 c0_level r1_depth r1_kind r1_sign))

abbrev shared_expr_Classification052_49 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification052_47 c0_level r1_depth r1_kind r1_sign))) ∨ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification052_48 c0_level r1_depth r1_kind r1_sign))))
theorem normalization_6143 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : (formula_122 c0_group c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification052_49 c0_group c0_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_5197 c0_group) (normalization_6136 c0_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_5197 c0_group)) (normalization_6142 c0_level r1_depth r1_kind r1_sign)))

theorem normalization_6144 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)) ↔ (¬ (shared_expr_Classification052_49 c0_group c0_level r1_depth r1_kind r1_sign)) := (not_congr (normalization_6143 c0_group c0_level r1_depth r1_kind r1_sign))

theorem normalization_6145 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign))) ↔ ((¬ ((c0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification052_49 c0_group c0_level r1_depth r1_kind r1_sign))) := (or_congr (normalization_5173 c0_mode) (or_congr (normalization_5174 c0_mode) (normalization_6144 c0_group c0_level r1_depth r1_kind r1_sign)))

theorem normalization_6146 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) ↔ (¬ ((¬ ((c0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification052_49 c0_group c0_level r1_depth r1_kind r1_sign)))) := (not_congr (normalization_6145 c0_group c0_level c0_mode r1_depth r1_kind r1_sign))

abbrev shared_expr_Classification052_50 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))))
theorem normalization_6147 (c0_level r1_depth r1_kind r1_sign : Int) : (formula_123 c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification052_50 c0_level r1_depth r1_kind r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6138 c0_level r1_depth) (or_congr (normalization_6140 c0_level r1_depth) (normalization_6116 r1_sign)))))

theorem normalization_6148 (c0_level r1_depth r1_kind r1_sign : Int) : (¬ (formula_123 c0_level r1_depth r1_kind r1_sign)) ↔ (¬ (shared_expr_Classification052_50 c0_level r1_depth r1_kind r1_sign)) := (not_congr (normalization_6147 c0_level r1_depth r1_kind r1_sign))

abbrev shared_expr_Classification052_51 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))))
theorem normalization_6149 (c0_level r1_depth r1_kind r1_sign : Int) : (formula_124 c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification052_51 c0_level r1_depth r1_kind r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6132 c0_level r1_depth) (or_congr (normalization_6134 c0_level r1_depth) (normalization_6116 r1_sign)))))

theorem normalization_6150 (c0_level r1_depth r1_kind r1_sign : Int) : (¬ (formula_124 c0_level r1_depth r1_kind r1_sign)) ↔ (¬ (shared_expr_Classification052_51 c0_level r1_depth r1_kind r1_sign)) := (not_congr (normalization_6149 c0_level r1_depth r1_kind r1_sign))

abbrev shared_expr_Classification052_52 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Classification052_50 c0_level r1_depth r1_kind r1_sign))) ∨ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification052_51 c0_level r1_depth r1_kind r1_sign))))
theorem normalization_6151 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : (formula_125 c0_group c0_level r1_depth r1_kind r1_sign) ↔ (shared_expr_Classification052_52 c0_group c0_level r1_depth r1_kind r1_sign) := (or_congr (and_congr (normalization_5197 c0_group) (normalization_6148 c0_level r1_depth r1_kind r1_sign)) (and_congr (not_congr (normalization_5197 c0_group)) (normalization_6150 c0_level r1_depth r1_kind r1_sign)))

theorem normalization_6152 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)) ↔ (¬ (shared_expr_Classification052_52 c0_group c0_level r1_depth r1_kind r1_sign)) := (not_congr (normalization_6151 c0_group c0_level r1_depth r1_kind r1_sign))

theorem normalization_6153 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign))) ↔ ((¬ ((c0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification052_52 c0_group c0_level r1_depth r1_kind r1_sign))) := (or_congr (normalization_5642 c0_mode) (or_congr (normalization_5644 c0_mode) (normalization_6152 c0_group c0_level r1_depth r1_kind r1_sign)))

theorem normalization_6154 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) ↔ (¬ ((¬ ((c0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification052_52 c0_group c0_level r1_depth r1_kind r1_sign)))) := (not_congr (normalization_6153 c0_group c0_level c0_mode r1_depth r1_kind r1_sign))

theorem normalization_6155 (r1_node : Int) : ((r1_node % (2 : Int)) ≤ (0 : Int)) ↔ (¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6156 (r1_node : Int) : (¬ ((r1_node % (2 : Int)) ≤ (0 : Int))) ↔ (¬ (¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6155 r1_node))

abbrev shared_expr_Classification052_53 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
theorem normalization_6157 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_126 c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_53 c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6111 r1_sign) (or_congr (normalization_6138 c0_level r1_depth) (or_congr (normalization_6140 c0_level r1_depth) (normalization_6156 r1_node))))))

theorem normalization_6158 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_126 c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_53 c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6157 c0_level r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_54 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification052_53 c0_level r1_depth r1_kind r1_node r1_sign))))
theorem normalization_6159 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_54 c0_group c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_5197 c0_group) (normalization_276 r1_kind)) (and_congr (not_congr (normalization_5197 c0_group)) (normalization_6158 c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6160 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_54 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6159 c0_group c0_level r1_depth r1_kind r1_node r1_sign))

theorem normalization_6161 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ↔ ((¬ ((c0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification052_54 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := (or_congr (normalization_5654 c0_mode) (or_congr (normalization_5656 c0_mode) (normalization_6160 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6162 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ↔ (¬ ((¬ ((c0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification052_54 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) := (not_congr (normalization_6161 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign))

theorem normalization_6163 (r1_node : Int) : ((r1_node % (2 : Int)) ≥ (1 : Int)) ↔ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6164 (r1_node : Int) : (¬ ((r1_node % (2 : Int)) ≥ (1 : Int))) ↔ (¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := (not_congr (normalization_6163 r1_node))

abbrev shared_expr_Classification052_55 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
theorem normalization_6165 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_128 c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_55 c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6111 r1_sign) (or_congr (normalization_6138 c0_level r1_depth) (or_congr (normalization_6140 c0_level r1_depth) (normalization_6164 r1_node))))))

theorem normalization_6166 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_128 c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_55 c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6165 c0_level r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_56 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification052_55 c0_level r1_depth r1_kind r1_node r1_sign))))
theorem normalization_6167 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_56 c0_group c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_5197 c0_group) (normalization_276 r1_kind)) (and_congr (not_congr (normalization_5197 c0_group)) (normalization_6166 c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6168 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_56 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6167 c0_group c0_level r1_depth r1_kind r1_node r1_sign))

theorem normalization_6169 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ↔ ((¬ ((c0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification052_56 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := (or_congr (normalization_5664 c0_mode) (or_congr (normalization_5666 c0_mode) (normalization_6168 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6170 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ↔ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification052_56 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) := (not_congr (normalization_6169 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_57 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
theorem normalization_6171 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_130 c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_57 c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6138 c0_level r1_depth) (or_congr (normalization_6140 c0_level r1_depth) (or_congr (normalization_6116 r1_sign) (normalization_6156 r1_node))))))

theorem normalization_6172 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_130 c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_57 c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6171 c0_level r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_58 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification052_57 c0_level r1_depth r1_kind r1_node r1_sign))))
theorem normalization_6173 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_58 c0_group c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_5197 c0_group) (normalization_276 r1_kind)) (and_congr (not_congr (normalization_5197 c0_group)) (normalization_6172 c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6174 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_58 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6173 c0_group c0_level r1_depth r1_kind r1_node r1_sign))

theorem normalization_6175 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ↔ ((¬ ((c0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification052_58 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := (or_congr (normalization_5674 c0_mode) (or_congr (normalization_5675 c0_mode) (normalization_6174 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6176 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ↔ (¬ ((¬ ((c0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification052_58 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) := (not_congr (normalization_6175 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_59 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
theorem normalization_6177 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_132 c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_59 c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_101 r1_kind) (or_congr (normalization_103 r1_kind) (or_congr (normalization_6138 c0_level r1_depth) (or_congr (normalization_6140 c0_level r1_depth) (or_congr (normalization_6116 r1_sign) (normalization_6164 r1_node))))))

theorem normalization_6178 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_132 c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_59 c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6177 c0_level r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_60 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Classification052_59 c0_level r1_depth r1_kind r1_node r1_sign))))
theorem normalization_6179 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_60 c0_group c0_level r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_5197 c0_group) (normalization_276 r1_kind)) (and_congr (not_congr (normalization_5197 c0_group)) (normalization_6178 c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6180 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ↔ (¬ (shared_expr_Classification052_60 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) := (not_congr (normalization_6179 c0_group c0_level r1_depth r1_kind r1_node r1_sign))

theorem normalization_6181 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ↔ ((¬ ((c0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification052_60 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := (or_congr (normalization_5683 c0_mode) (or_congr (normalization_5685 c0_mode) (normalization_6180 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))

theorem normalization_6182 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ↔ (¬ ((¬ ((c0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification052_60 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) := (not_congr (normalization_6181 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_61 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((c0_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Classification052_49 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ ((c0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Classification052_52 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ ((c0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Classification052_54 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Classification052_56 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ ((c0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Classification052_58 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ ((c0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Classification052_60 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))))
theorem normalization_6183 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_61 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) := (or_congr (normalization_6146 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (or_congr (normalization_6154 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (or_congr (normalization_6162 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_6170 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (or_congr (normalization_6176 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (normalization_6182 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign))))))

abbrev shared_expr_Classification052_62 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_63 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_64 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification052_62 c0_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification052_63 c0_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Classification052_65 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_66 (c0_level r1_depth r1_kind r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_67 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification052_65 c0_level r1_depth r1_kind r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (shared_expr_Classification052_66 c0_level r1_depth r1_kind r1_sign)))
abbrev shared_expr_Classification052_68 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification052_69 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification052_68 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_70 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification052_71 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification052_70 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_72 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification052_73 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification052_72 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_74 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((c0_level + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∨ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r1_node / (2 : Int))) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Classification052_75 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∧ (shared_expr_Classification052_74 c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int))))) ∧ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))))
abbrev shared_expr_Classification052_76 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_mode) ≤ (0 : Int)) ∧ (¬ ((c0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Classification052_64 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((((c0_mode) ≤ (1 : Int)) ∧ (¬ ((c0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Classification052_67 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((((c0_mode) ≤ (2 : Int)) ∧ (¬ ((c0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Classification052_69 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (3 : Int)) ∧ (¬ ((c0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Classification052_71 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (4 : Int)) ∧ (¬ ((c0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification052_73 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((((c0_mode) ≤ (5 : Int)) ∧ (¬ ((c0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Classification052_75 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))
theorem normalization_6184 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : ((formula_1730 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) ↔ (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ↔ ((shared_expr_Classification052_76 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_61 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) := (iff_congr (normalization_5877 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (normalization_6183 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign))

abbrev shared_expr_Classification052_77 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification052_61 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
theorem normalization_6185 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_1760 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_77 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_3515 c0_kind) (normalization_6183 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (and_congr (not_congr (normalization_3515 c0_kind)) (normalization_6128 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Classification052_78 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification052_76 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification052_42 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev shared_expr_Classification052_79 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((shared_expr_Classification052_78 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_77 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
theorem normalization_6186 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_1761 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_79 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := (iff_congr (normalization_5895 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (normalization_6185 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2749 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_1761 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := by
  classical
  have ht := (normalized_1468 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))) (shared_expr_Classification052_76 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (shared_expr_Classification052_61 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (shared_expr_Classification052_42 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (shared_expr_Classification052_41 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign))
  have n0 : ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3517 c0_kind) (replay_1292 c0_kind)
  have n1 : ((shared_expr_Classification052_76 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Classification052_61 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) := by
    exact Iff.mp (normalization_6184 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (replay_2700 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)
  have n2 : (shared_expr_Classification052_43 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) := by
    exact Iff.mp (normalization_6129 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) (replay_2748 c0_depth c0_kind c0_node c0_sign h r1_depth r1_kind r1_node r1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_6186 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign) hn

end H4Formal.Generated.Classification
