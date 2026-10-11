import H4Formal.Certificates.CheckedClassification.Classification043

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_1217 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5018 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5019 (c0_node c1_node : Int) : ((c0_node ≤ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (iff_congr (normalization_5014 c0_node c1_node) (normalization_5018 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2368 (c0_node c1_node : Int) : ((c0_node ≤ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1217 ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5019 c0_node c1_node) hn

theorem normalized_1218 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5020 (c0_node c1_node : Int) : ((c0_node ≥ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_5015 c0_node c1_node) (normalization_4946 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2369 (c0_node c1_node : Int) : ((c0_node ≥ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1218 ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5020 c0_node c1_node) hn

theorem normalized_1219 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5021 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_5018 c0_node c1_node) (normalization_4946 c0_node c1_node))

abbrev shared_expr_Classification044_0 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
theorem normalization_5022 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ↔ (shared_expr_Classification044_0 c0_node c1_node) := (iff_congr (normalization_5016 c0_node c1_node) (normalization_5021 c0_node c1_node))

-- Checked replay of monotonicity.
theorem replay_2370 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1219 ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
  have n0 : (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5019 c0_node c1_node) (replay_2368 c0_node c1_node)
  have n1 : ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5020 c0_node c1_node) (replay_2369 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5022 c0_node c1_node) hn

abbrev shared_expr_Classification044_1 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))))
abbrev formula_1474 (c0_node c1_node : Int) : Prop := (shared_expr_Classification044_1 c0_node c1_node)

theorem normalized_1220 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5023 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (not_congr (normalization_5018 c0_node c1_node))

theorem normalization_5024 (c0_node c1_node : Int) : ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ↔ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) := (or_congr (normalization_5023 c0_node c1_node) (normalization_4947 c0_node c1_node))

theorem normalization_5025 (c0_node c1_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_5024 c0_node c1_node))

abbrev shared_expr_Classification044_2 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))))
theorem normalization_5026 (c0_node c1_node : Int) : (formula_1474 c0_node c1_node) ↔ (shared_expr_Classification044_2 c0_node c1_node) := (iff_congr (normalization_5021 c0_node c1_node) (normalization_5025 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2371 (c0_node c1_node : Int) : (formula_1474 c0_node c1_node) := by
  classical
  have ht := (normalized_1220 ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5026 c0_node c1_node) hn

theorem normalized_1221 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5027 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification044_2 c0_node c1_node) := (iff_congr (normalization_5016 c0_node c1_node) (normalization_5025 c0_node c1_node))

-- Checked replay of trans.
theorem replay_2372 (c0_node c1_node : Int) : (((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1221 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) (shared_expr_Classification044_2 c0_node c1_node))
  have n0 : (shared_expr_Classification044_0 c0_node c1_node) := by
    exact Iff.mp (normalization_5022 c0_node c1_node) (replay_2370 c0_node c1_node)
  have n1 : (shared_expr_Classification044_2 c0_node c1_node) := by
    exact Iff.mp (normalization_5026 c0_node c1_node) (replay_2371 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5027 c0_node c1_node) hn

theorem normalized_1222 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5028 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification044_2 c0_node c1_node) := (iff_congr (normalization_4881 c0_node c1_node) (normalization_5025 c0_node c1_node))

-- Checked replay of trans.
theorem replay_2373 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1222 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) (shared_expr_Classification044_2 c0_node c1_node))
  have n0 : (shared_expr_Classification044_0 c0_node c1_node) := by
    exact Iff.mp (normalization_5017 c0_node c1_node) (replay_2367 c0_node c1_node)
  have n1 : (shared_expr_Classification044_2 c0_node c1_node) := by
    exact Iff.mp (normalization_5027 c0_node c1_node) (replay_2372 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5028 c0_node c1_node) hn

theorem normalized_1223 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5029 (c0_sign c1_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := (and_congr (normalization_3582 c0_sign) (normalization_1626 c1_sign))

abbrev shared_expr_Classification044_3 (c0_sign c1_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))))
theorem normalization_5030 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))) ↔ (shared_expr_Classification044_3 c0_sign c1_sign) := (iff_congr (normalization_4882 c0_sign c1_sign) (normalization_5029 c0_sign c1_sign))

-- Checked replay of monotonicity.
theorem replay_2374 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_1223 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have n1 : ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1719 c1_sign) (replay_648 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5030 c0_sign c1_sign) hn

abbrev shared_expr_Classification044_4 (c0_sign c1_sign : Int) : Prop := (((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev formula_1475 (c0_sign c1_sign : Int) : Prop := (shared_expr_Classification044_4 c0_sign c1_sign)

theorem normalized_1224 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5031 (c0_sign c1_sign : Int) : ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))) ↔ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) := (or_congr (normalization_3579 c0_sign) (or_congr (normalization_3580 c0_sign) (or_congr (normalization_1622 c1_sign) (normalization_1624 c1_sign))))

theorem normalization_5032 (c0_sign c1_sign : Int) : (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) := (not_congr (normalization_5031 c0_sign c1_sign))

abbrev shared_expr_Classification044_5 (c0_sign c1_sign : Int) : Prop := (((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))))
theorem normalization_5033 (c0_sign c1_sign : Int) : (formula_1475 c0_sign c1_sign) ↔ (shared_expr_Classification044_5 c0_sign c1_sign) := (iff_congr (normalization_5029 c0_sign c1_sign) (normalization_5032 c0_sign c1_sign))

-- Checked replay of rewrite.
theorem replay_2375 (c0_sign c1_sign : Int) : (formula_1475 c0_sign c1_sign) := by
  classical
  have ht := (normalized_1224 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c1_sign) ≤ (1 : Int)) ((c1_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5033 c0_sign c1_sign) hn

theorem normalized_1225 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_6 (c0_sign c1_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))))
theorem normalization_5034 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) ↔ (shared_expr_Classification044_6 c0_sign c1_sign) := (iff_congr (normalization_4882 c0_sign c1_sign) (normalization_5032 c0_sign c1_sign))

-- Checked replay of trans.
theorem replay_2376 (c0_sign c1_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1225 ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification044_3 c0_sign c1_sign) := by
    exact Iff.mp (normalization_5030 c0_sign c1_sign) (replay_2374 c0_sign c1_sign)
  have n1 : (shared_expr_Classification044_5 c0_sign c1_sign) := by
    exact Iff.mp (normalization_5033 c0_sign c1_sign) (replay_2375 c0_sign c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5034 c0_sign c1_sign) hn

abbrev shared_expr_Classification044_7 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification044_8 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_7 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))
abbrev formula_1476 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_8 c0_node c0_sign c1_node c1_sign)

abbrev shared_expr_Classification044_9 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (formula_1476 c0_node c0_sign c1_node c1_sign))
abbrev formula_1477 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_9 c0_node c0_sign c1_node c1_sign)

theorem normalized_1226 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_10 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification044_11 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_10 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))
theorem normalization_5035 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1476 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_11 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_5025 c0_node c1_node) (normalization_5032 c0_sign c1_sign)) (and_congr (not_congr (normalization_5025 c0_node c1_node)) (normalization_4947 c0_node c1_node)))

abbrev shared_expr_Classification044_12 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification044_13 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_12 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))
theorem normalization_5036 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1477 c0_node c0_sign c1_node c1_sign) ↔ ((shared_expr_Classification044_13 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_11 c0_node c0_sign c1_node c1_sign)) := (iff_congr (normalization_4948 c0_node c0_sign c1_node c1_sign) (normalization_5035 c0_node c0_sign c1_node c1_sign))

-- Checked replay of monotonicity.
theorem replay_2377 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1477 c0_node c0_sign c1_node c1_sign) := by
  classical
  have ht := (normalized_1226 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification044_2 c0_node c1_node) := by
    exact Iff.mp (normalization_5028 c0_node c1_node) (replay_2373 c0_node c1_node)
  have n1 : (shared_expr_Classification044_6 c0_sign c1_sign) := by
    exact Iff.mp (normalization_5034 c0_sign c1_sign) (replay_2376 c0_sign c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5036 c0_node c0_sign c1_node c1_sign) hn

theorem normalized_1227 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_14 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Classification044_10 c0_node c0_sign c1_node c1_sign))
theorem normalization_5037 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1444 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_5024 c0_node c1_node) (normalization_4947 c0_node c1_node)) (and_congr (not_congr (normalization_5024 c0_node c1_node)) (normalization_5032 c0_sign c1_sign)))

theorem normalization_5038 (c0_node c0_sign c1_node c1_sign : Int) : ((formula_1476 c0_node c0_sign c1_node c1_sign) ↔ (formula_1444 c0_node c0_sign c1_node c1_sign)) ↔ ((shared_expr_Classification044_11 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign)) := (iff_congr (normalization_5035 c0_node c0_sign c1_node c1_sign) (normalization_5037 c0_node c0_sign c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2378 (c0_node c0_sign c1_node c1_sign : Int) : ((formula_1476 c0_node c0_sign c1_node c1_sign) ↔ (formula_1444 c0_node c0_sign c1_node c1_sign)) := by
  classical
  have ht := (normalized_1227 ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5038 c0_node c0_sign c1_node c1_sign) hn

abbrev shared_expr_Classification044_15 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (formula_1444 c0_node c0_sign c1_node c1_sign))
abbrev formula_1478 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_15 c0_node c0_sign c1_node c1_sign)

theorem normalized_1228 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5039 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1478 c0_node c0_sign c1_node c1_sign) ↔ ((shared_expr_Classification044_13 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign)) := (iff_congr (normalization_4948 c0_node c0_sign c1_node c1_sign) (normalization_5037 c0_node c0_sign c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2379 (c0_node c0_sign c1_node c1_sign : Int) : (formula_1478 c0_node c0_sign c1_node c1_sign) := by
  classical
  have ht := (normalized_1228 (shared_expr_Classification044_13 c0_node c0_sign c1_node c1_sign) (shared_expr_Classification044_11 c0_node c0_sign c1_node c1_sign) (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign))
  have n0 : ((shared_expr_Classification044_13 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_11 c0_node c0_sign c1_node c1_sign)) := by
    exact Iff.mp (normalization_5036 c0_node c0_sign c1_node c1_sign) (replay_2377 c0_node c0_sign c1_node c1_sign)
  have n1 : ((shared_expr_Classification044_11 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign)) := by
    exact Iff.mp (normalization_5038 c0_node c0_sign c1_node c1_sign) (replay_2378 c0_node c0_sign c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5039 c0_node c0_sign c1_node c1_sign) hn

theorem normalized_1229 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5040 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5041 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_5042 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_5040 c0_depth c1_depth) (normalization_5041 c0_depth c1_depth))

abbrev shared_expr_Classification044_16 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))
theorem normalization_5043 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Classification044_16 c0_depth c1_depth) := (iff_congr (normalization_4949 c0_depth c1_depth) (normalization_5042 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2380 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_1229 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5043 c0_depth c1_depth) hn

abbrev shared_expr_Classification044_17 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))))))
abbrev formula_1479 (c0_depth c1_depth : Int) : Prop := (shared_expr_Classification044_17 c0_depth c1_depth)

theorem normalized_1230 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5044 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) := (not_congr (normalization_5040 c0_depth c1_depth))

theorem normalization_5045 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_5041 c0_depth c1_depth))

theorem normalization_5046 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_5044 c0_depth c1_depth) (normalization_5045 c0_depth c1_depth))

theorem normalization_5047 (c0_depth c1_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_5046 c0_depth c1_depth))

abbrev shared_expr_Classification044_18 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))))
theorem normalization_5048 (c0_depth c1_depth : Int) : (formula_1479 c0_depth c1_depth) ↔ (shared_expr_Classification044_18 c0_depth c1_depth) := (iff_congr (normalization_5042 c0_depth c1_depth) (normalization_5047 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2381 (c0_depth c1_depth : Int) : (formula_1479 c0_depth c1_depth) := by
  classical
  have ht := (normalized_1230 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5048 c0_depth c1_depth) hn

theorem normalized_1231 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5049 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Classification044_18 c0_depth c1_depth) := (iff_congr (normalization_4949 c0_depth c1_depth) (normalization_5047 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2382 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_1231 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) (shared_expr_Classification044_18 c0_depth c1_depth))
  have n0 : (shared_expr_Classification044_16 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5043 c0_depth c1_depth) (replay_2380 c0_depth c1_depth)
  have n1 : (shared_expr_Classification044_18 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5048 c0_depth c1_depth) (replay_2381 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5049 c0_depth c1_depth) hn

theorem normalized_1232 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5050 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5051 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (and_congr (normalization_5050 c0_node c1_node) (normalization_4951 c0_node c1_node))

abbrev shared_expr_Classification044_19 (c0_node c1_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_5052 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification044_19 c0_node c1_node) := (iff_congr (normalization_4950 c0_node c1_node) (normalization_5051 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2383 (c0_node c1_node : Int) : (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1232 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5052 c0_node c1_node) hn

abbrev shared_expr_Classification044_20 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1480 (c0_node c1_node : Int) : Prop := (shared_expr_Classification044_20 c0_node c1_node)

theorem normalized_1233 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5053 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5050 c0_node c1_node))

theorem normalization_5054 (c0_node c1_node : Int) : ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) := (or_congr (normalization_5053 c0_node c1_node) (normalization_4952 c0_node c1_node))

theorem normalization_5055 (c0_node c1_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) := (not_congr (normalization_5054 c0_node c1_node))

abbrev shared_expr_Classification044_21 (c0_node c1_node : Int) : Prop := (((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
theorem normalization_5056 (c0_node c1_node : Int) : (formula_1480 c0_node c1_node) ↔ (shared_expr_Classification044_21 c0_node c1_node) := (iff_congr (normalization_5051 c0_node c1_node) (normalization_5055 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2384 (c0_node c1_node : Int) : (formula_1480 c0_node c1_node) := by
  classical
  have ht := (normalized_1233 (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5056 c0_node c1_node) hn

abbrev shared_expr_Classification044_22 (c0_node c1_node : Int) : Prop := (((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1481 (c0_node c1_node : Int) : Prop := (shared_expr_Classification044_22 c0_node c1_node)

theorem normalized_1234 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5057 (c0_node c1_node : Int) : (formula_1481 c0_node c1_node) ↔ (shared_expr_Classification044_21 c0_node c1_node) := (iff_congr (normalization_4950 c0_node c1_node) (normalization_5055 c0_node c1_node))

-- Checked replay of trans.
theorem replay_2385 (c0_node c1_node : Int) : (formula_1481 c0_node c1_node) := by
  classical
  have ht := (normalized_1234 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) (shared_expr_Classification044_21 c0_node c1_node))
  have n0 : (shared_expr_Classification044_19 c0_node c1_node) := by
    exact Iff.mp (normalization_5052 c0_node c1_node) (replay_2383 c0_node c1_node)
  have n1 : (shared_expr_Classification044_21 c0_node c1_node) := by
    exact Iff.mp (normalization_5056 c0_node c1_node) (replay_2384 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5057 c0_node c1_node) hn

abbrev shared_expr_Classification044_23 (c0_node c0_sign c1_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev shared_expr_Classification044_24 (c0_node c1_node : Int) : Prop := ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_1482 (c0_node c0_sign c1_node : Int) : Prop := ((shared_expr_Classification044_23 c0_node c0_sign c1_node) ∨ (shared_expr_Classification044_24 c0_node c1_node))

theorem normalized_1235 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_25 (c0_node c0_sign c1_node : Int) : Prop := ((¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Classification044_26 (c0_node c1_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))))) ∧ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_5058 (c0_node c0_sign c1_node : Int) : (formula_1482 c0_node c0_sign c1_node) ↔ ((shared_expr_Classification044_25 c0_node c0_sign c1_node) ∨ (shared_expr_Classification044_26 c0_node c1_node)) := (or_congr (and_congr (normalization_5055 c0_node c1_node) (normalization_3582 c0_sign)) (and_congr (not_congr (normalization_5055 c0_node c1_node)) (normalization_4952 c0_node c1_node)))

abbrev shared_expr_Classification044_27 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification044_28 (c0_node c0_sign c1_node : Int) : Prop := ((((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification044_27 c0_node c1_node))
theorem normalization_5059 (c0_node c0_sign c1_node : Int) : ((formula_1464 c0_node c0_sign c1_node) ↔ (formula_1482 c0_node c0_sign c1_node)) ↔ ((shared_expr_Classification044_28 c0_node c0_sign c1_node) ↔ ((shared_expr_Classification044_25 c0_node c0_sign c1_node) ∨ (shared_expr_Classification044_26 c0_node c1_node))) := (iff_congr (normalization_4953 c0_node c0_sign c1_node) (normalization_5058 c0_node c0_sign c1_node))

-- Checked replay of monotonicity.
theorem replay_2386 (c0_node c0_sign c1_node : Int) : ((formula_1464 c0_node c0_sign c1_node) ↔ (formula_1482 c0_node c0_sign c1_node)) := by
  classical
  have ht := (normalized_1235 ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Classification044_21 c0_node c1_node) := by
    exact Iff.mp (normalization_5057 c0_node c1_node) (replay_2385 c0_node c1_node)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3584 c0_sign) (replay_1316 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5059 c0_node c0_sign c1_node) hn

theorem normalized_1236 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_29 (c0_node c1_node : Int) : Prop := (((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_5060 (c0_node c0_sign c1_node : Int) : (formula_1442 c0_node c0_sign c1_node) ↔ ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node)) := (or_congr (and_congr (normalization_5054 c0_node c1_node) (normalization_4952 c0_node c1_node)) (and_congr (not_congr (normalization_5054 c0_node c1_node)) (normalization_3582 c0_sign)))

abbrev shared_expr_Classification044_30 (c0_node c0_sign c1_node : Int) : Prop := (((shared_expr_Classification044_25 c0_node c0_sign c1_node) ∨ (shared_expr_Classification044_26 c0_node c1_node)) ↔ ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node)))
theorem normalization_5061 (c0_node c0_sign c1_node : Int) : ((formula_1482 c0_node c0_sign c1_node) ↔ (formula_1442 c0_node c0_sign c1_node)) ↔ (shared_expr_Classification044_30 c0_node c0_sign c1_node) := (iff_congr (normalization_5058 c0_node c0_sign c1_node) (normalization_5060 c0_node c0_sign c1_node))

-- Checked replay of rewrite.
theorem replay_2387 (c0_node c0_sign c1_node : Int) : ((formula_1482 c0_node c0_sign c1_node) ↔ (formula_1442 c0_node c0_sign c1_node)) := by
  classical
  have ht := (normalized_1236 ((¬ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5061 c0_node c0_sign c1_node) hn

theorem normalized_1237 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5062 (c0_node c0_sign c1_node : Int) : ((formula_1464 c0_node c0_sign c1_node) ↔ (formula_1442 c0_node c0_sign c1_node)) ↔ ((shared_expr_Classification044_28 c0_node c0_sign c1_node) ↔ ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node))) := (iff_congr (normalization_4953 c0_node c0_sign c1_node) (normalization_5060 c0_node c0_sign c1_node))

-- Checked replay of trans.
theorem replay_2388 (c0_node c0_sign c1_node : Int) : ((formula_1464 c0_node c0_sign c1_node) ↔ (formula_1442 c0_node c0_sign c1_node)) := by
  classical
  have ht := (normalized_1237 (shared_expr_Classification044_28 c0_node c0_sign c1_node) ((shared_expr_Classification044_25 c0_node c0_sign c1_node) ∨ (shared_expr_Classification044_26 c0_node c1_node)) ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node)))
  have n0 : ((shared_expr_Classification044_28 c0_node c0_sign c1_node) ↔ ((shared_expr_Classification044_25 c0_node c0_sign c1_node) ∨ (shared_expr_Classification044_26 c0_node c1_node))) := by
    exact Iff.mp (normalization_5059 c0_node c0_sign c1_node) (replay_2386 c0_node c0_sign c1_node)
  have n1 : (shared_expr_Classification044_30 c0_node c0_sign c1_node) := by
    exact Iff.mp (normalization_5061 c0_node c0_sign c1_node) (replay_2387 c0_node c0_sign c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5062 c0_node c0_sign c1_node) hn

theorem normalized_1238 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5063 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_5064 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_5065 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) := (and_congr (normalization_5063 c0_depth c1_depth) (normalization_5064 c0_depth c1_depth))

abbrev shared_expr_Classification044_31 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))))
theorem normalization_5066 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ↔ (shared_expr_Classification044_31 c0_depth c1_depth) := (iff_congr (normalization_4954 c0_depth c1_depth) (normalization_5065 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2389 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1238 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5066 c0_depth c1_depth) hn

abbrev shared_expr_Classification044_32 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))))
abbrev formula_1483 (c0_depth c1_depth : Int) : Prop := (shared_expr_Classification044_32 c0_depth c1_depth)

theorem normalized_1239 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5067 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) := (not_congr (normalization_5063 c0_depth c1_depth))

theorem normalization_5068 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) := (not_congr (normalization_5064 c0_depth c1_depth))

theorem normalization_5069 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) := (or_congr (normalization_5067 c0_depth c1_depth) (normalization_5068 c0_depth c1_depth))

theorem normalization_5070 (c0_depth c1_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))))) := (not_congr (normalization_5069 c0_depth c1_depth))

abbrev shared_expr_Classification044_33 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))))))
theorem normalization_5071 (c0_depth c1_depth : Int) : (formula_1483 c0_depth c1_depth) ↔ (shared_expr_Classification044_33 c0_depth c1_depth) := (iff_congr (normalization_5065 c0_depth c1_depth) (normalization_5070 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2390 (c0_depth c1_depth : Int) : (formula_1483 c0_depth c1_depth) := by
  classical
  have ht := (normalized_1239 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5071 c0_depth c1_depth) hn

theorem normalized_1240 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5072 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) ↔ (shared_expr_Classification044_33 c0_depth c1_depth) := (iff_congr (normalization_4954 c0_depth c1_depth) (normalization_5070 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2391 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1240 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) (shared_expr_Classification044_33 c0_depth c1_depth))
  have n0 : (shared_expr_Classification044_31 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5066 c0_depth c1_depth) (replay_2389 c0_depth c1_depth)
  have n1 : (shared_expr_Classification044_33 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5071 c0_depth c1_depth) (replay_2390 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5072 c0_depth c1_depth) hn

theorem normalized_1241 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5073 (c0_depth c1_depth : Int) : (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))) := (not_congr (normalization_5070 c0_depth c1_depth))

abbrev shared_expr_Classification044_34 (c0_depth c1_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))))
theorem normalization_5074 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))))) ↔ (shared_expr_Classification044_34 c0_depth c1_depth) := (iff_congr (normalization_4955 c0_depth c1_depth) (normalization_5073 c0_depth c1_depth))

-- Checked replay of monotonicity.
theorem replay_2392 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ↔ (¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_1241 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification044_33 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5072 c0_depth c1_depth) (replay_2391 c0_depth c1_depth)
  have hn := ht n0
  exact Iff.mpr (normalization_5074 c0_depth c1_depth) hn

abbrev shared_expr_Classification044_35 (c0_depth c1_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))))
abbrev formula_1484 (c0_depth c1_depth : Int) : Prop := (shared_expr_Classification044_35 c0_depth c1_depth)

theorem normalized_1242 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_36 (c0_depth c1_depth : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))
theorem normalization_5075 (c0_depth c1_depth : Int) : (formula_1484 c0_depth c1_depth) ↔ (shared_expr_Classification044_36 c0_depth c1_depth) := (iff_congr (normalization_5073 c0_depth c1_depth) (normalization_5069 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2393 (c0_depth c1_depth : Int) : (formula_1484 c0_depth c1_depth) := by
  classical
  have ht := (normalized_1242 ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_5075 c0_depth c1_depth) hn

theorem normalized_1243 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_37 (c0_depth c1_depth : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))
theorem normalization_5076 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) ↔ (shared_expr_Classification044_37 c0_depth c1_depth) := (iff_congr (normalization_4955 c0_depth c1_depth) (normalization_5069 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2394 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))) := by
  classical
  have ht := (normalized_1243 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))))
  have n0 : (shared_expr_Classification044_34 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5074 c0_depth c1_depth) (replay_2392 c0_depth c1_depth)
  have n1 : (shared_expr_Classification044_36 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5075 c0_depth c1_depth) (replay_2393 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5076 c0_depth c1_depth) hn

theorem normalized_1244 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5077 (c0_node c1_node : Int) : ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5078 (c0_node c1_node : Int) : (((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (and_congr (normalization_4957 c0_node c1_node) (normalization_5077 c0_node c1_node))

abbrev shared_expr_Classification044_38 (c0_node c1_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_5079 (c0_node c1_node : Int) : (((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Classification044_38 c0_node c1_node) := (iff_congr (normalization_4956 c0_node c1_node) (normalization_5078 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2395 (c0_node c1_node : Int) : (((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1244 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_5079 c0_node c1_node) hn

abbrev shared_expr_Classification044_39 (c0_node c1_node : Int) : Prop := ((((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1485 (c0_node c1_node : Int) : Prop := (shared_expr_Classification044_39 c0_node c1_node)

theorem normalized_1245 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5080 (c0_node c1_node : Int) : (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (not_congr (normalization_5077 c0_node c1_node))

theorem normalization_5081 (c0_node c1_node : Int) : ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) := (or_congr (normalization_4958 c0_node c1_node) (normalization_5080 c0_node c1_node))

theorem normalization_5082 (c0_node c1_node : Int) : (¬ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) := (not_congr (normalization_5081 c0_node c1_node))

abbrev shared_expr_Classification044_40 (c0_node c1_node : Int) : Prop := (((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))))
theorem normalization_5083 (c0_node c1_node : Int) : (formula_1485 c0_node c1_node) ↔ (shared_expr_Classification044_40 c0_node c1_node) := (iff_congr (normalization_5078 c0_node c1_node) (normalization_5082 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2396 (c0_node c1_node : Int) : (formula_1485 c0_node c1_node) := by
  classical
  have ht := (normalized_1245 (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5083 c0_node c1_node) hn

abbrev shared_expr_Classification044_41 (c0_node c1_node : Int) : Prop := (((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_1486 (c0_node c1_node : Int) : Prop := (shared_expr_Classification044_41 c0_node c1_node)

theorem normalized_1246 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5084 (c0_node c1_node : Int) : (formula_1486 c0_node c1_node) ↔ (shared_expr_Classification044_40 c0_node c1_node) := (iff_congr (normalization_4956 c0_node c1_node) (normalization_5082 c0_node c1_node))

-- Checked replay of trans.
theorem replay_2397 (c0_node c1_node : Int) : (formula_1486 c0_node c1_node) := by
  classical
  have ht := (normalized_1246 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) (shared_expr_Classification044_40 c0_node c1_node))
  have n0 : (shared_expr_Classification044_38 c0_node c1_node) := by
    exact Iff.mp (normalization_5079 c0_node c1_node) (replay_2395 c0_node c1_node)
  have n1 : (shared_expr_Classification044_40 c0_node c1_node) := by
    exact Iff.mp (normalization_5083 c0_node c1_node) (replay_2396 c0_node c1_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5084 c0_node c1_node) hn

abbrev shared_expr_Classification044_42 (c0_node c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification044_43 (c0_node c1_node : Int) : Prop := ((¬ (¬ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_1487 (c0_node c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_42 c0_node c1_node c1_sign) ∨ (shared_expr_Classification044_43 c0_node c1_node))

theorem normalized_1247 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_44 (c0_node c1_node c1_sign : Int) : Prop := ((¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Classification044_45 (c0_node c1_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
theorem normalization_5085 (c0_node c1_node c1_sign : Int) : (formula_1487 c0_node c1_node c1_sign) ↔ ((shared_expr_Classification044_44 c0_node c1_node c1_sign) ∨ (shared_expr_Classification044_45 c0_node c1_node)) := (or_congr (and_congr (normalization_5082 c0_node c1_node) (normalization_1626 c1_sign)) (and_congr (not_congr (normalization_5082 c0_node c1_node)) (normalization_4958 c0_node c1_node)))

abbrev shared_expr_Classification044_46 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification044_47 (c0_node c1_node c1_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification044_46 c0_node c1_node))
theorem normalization_5086 (c0_node c1_node c1_sign : Int) : ((formula_1465 c0_node c1_node c1_sign) ↔ (formula_1487 c0_node c1_node c1_sign)) ↔ ((shared_expr_Classification044_47 c0_node c1_node c1_sign) ↔ ((shared_expr_Classification044_44 c0_node c1_node c1_sign) ∨ (shared_expr_Classification044_45 c0_node c1_node))) := (iff_congr (normalization_4959 c0_node c1_node c1_sign) (normalization_5085 c0_node c1_node c1_sign))

-- Checked replay of monotonicity.
theorem replay_2398 (c0_node c1_node c1_sign : Int) : ((formula_1465 c0_node c1_node c1_sign) ↔ (formula_1487 c0_node c1_node c1_sign)) := by
  classical
  have ht := (normalized_1247 ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Classification044_40 c0_node c1_node) := by
    exact Iff.mp (normalization_5084 c0_node c1_node) (replay_2397 c0_node c1_node)
  have n1 : ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1719 c1_sign) (replay_648 c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5086 c0_node c1_node c1_sign) hn

theorem normalized_1248 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_48 (c0_node c1_node : Int) : Prop := (((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
theorem normalization_5087 (c0_node c1_node c1_sign : Int) : (formula_1441 c0_node c1_node c1_sign) ↔ ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign)) := (or_congr (and_congr (normalization_5081 c0_node c1_node) (normalization_4958 c0_node c1_node)) (and_congr (not_congr (normalization_5081 c0_node c1_node)) (normalization_1626 c1_sign)))

abbrev shared_expr_Classification044_49 (c0_node c1_node c1_sign : Int) : Prop := (((shared_expr_Classification044_44 c0_node c1_node c1_sign) ∨ (shared_expr_Classification044_45 c0_node c1_node)) ↔ ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign)))
theorem normalization_5088 (c0_node c1_node c1_sign : Int) : ((formula_1487 c0_node c1_node c1_sign) ↔ (formula_1441 c0_node c1_node c1_sign)) ↔ (shared_expr_Classification044_49 c0_node c1_node c1_sign) := (iff_congr (normalization_5085 c0_node c1_node c1_sign) (normalization_5087 c0_node c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2399 (c0_node c1_node c1_sign : Int) : ((formula_1487 c0_node c1_node c1_sign) ↔ (formula_1441 c0_node c1_node c1_sign)) := by
  classical
  have ht := (normalized_1248 ((¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∨ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int))))) (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5088 c0_node c1_node c1_sign) hn

theorem normalized_1249 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5089 (c0_node c1_node c1_sign : Int) : ((formula_1465 c0_node c1_node c1_sign) ↔ (formula_1441 c0_node c1_node c1_sign)) ↔ ((shared_expr_Classification044_47 c0_node c1_node c1_sign) ↔ ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign))) := (iff_congr (normalization_4959 c0_node c1_node c1_sign) (normalization_5087 c0_node c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2400 (c0_node c1_node c1_sign : Int) : ((formula_1465 c0_node c1_node c1_sign) ↔ (formula_1441 c0_node c1_node c1_sign)) := by
  classical
  have ht := (normalized_1249 (shared_expr_Classification044_47 c0_node c1_node c1_sign) ((shared_expr_Classification044_44 c0_node c1_node c1_sign) ∨ (shared_expr_Classification044_45 c0_node c1_node)) ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign)))
  have n0 : ((shared_expr_Classification044_47 c0_node c1_node c1_sign) ↔ ((shared_expr_Classification044_44 c0_node c1_node c1_sign) ∨ (shared_expr_Classification044_45 c0_node c1_node))) := by
    exact Iff.mp (normalization_5086 c0_node c1_node c1_sign) (replay_2398 c0_node c1_node c1_sign)
  have n1 : (shared_expr_Classification044_49 c0_node c1_node c1_sign) := by
    exact Iff.mp (normalization_5088 c0_node c1_node c1_sign) (replay_2399 c0_node c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5089 c0_node c1_node c1_sign) hn

abbrev shared_expr_Classification044_50 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ∨ (formula_1465 c0_node c1_node c1_sign)) ↔ (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ∨ (formula_1441 c0_node c1_node c1_sign)))
abbrev formula_1488 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_50 c0_depth c0_node c1_depth c1_node c1_sign)

theorem normalized_1250 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_51 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign)))
theorem normalization_5090 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ∨ (formula_1441 c0_node c1_node c1_sign)) ↔ (shared_expr_Classification044_51 c0_depth c0_node c1_depth c1_node c1_sign) := (or_congr (normalization_5069 c0_depth c1_depth) (normalization_5087 c0_node c1_node c1_sign))

abbrev shared_expr_Classification044_52 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification044_47 c0_node c1_node c1_sign)) ↔ (shared_expr_Classification044_51 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_5091 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1488 c0_depth c0_node c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_52 c0_depth c0_node c1_depth c1_node c1_sign) := (iff_congr (normalization_4960 c0_depth c0_node c1_depth c1_node c1_sign) (normalization_5090 c0_depth c0_node c1_depth c1_node c1_sign))

-- Checked replay of monotonicity.
theorem replay_2401 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1488 c0_depth c0_node c1_depth c1_node c1_sign) := by
  classical
  have ht := (normalized_1250 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) (shared_expr_Classification044_47 c0_node c1_node c1_sign) ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign)))
  have n0 : (shared_expr_Classification044_37 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5076 c0_depth c1_depth) (replay_2394 c0_depth c1_depth)
  have n1 : ((shared_expr_Classification044_47 c0_node c1_node c1_sign) ↔ ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign))) := by
    exact Iff.mp (normalization_5089 c0_node c1_node c1_sign) (replay_2400 c0_node c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5091 c0_depth c0_node c1_depth c1_node c1_sign) hn

abbrev shared_expr_Classification044_53 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))) ∨ (formula_1441 c0_node c1_node c1_sign)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ∨ (formula_1441 c0_node c1_node c1_sign)))
abbrev formula_1489 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_53 c0_depth c0_node c1_depth c1_node c1_sign)

theorem normalized_1251 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_54 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) ∨ ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign)))
theorem normalization_5092 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ∨ (formula_1441 c0_node c1_node c1_sign)) ↔ (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign) := (or_congr (normalization_5067 c0_depth c1_depth) (or_congr (normalization_5068 c0_depth c1_depth) (normalization_5087 c0_node c1_node c1_sign)))

theorem normalization_5093 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1489 c0_depth c0_node c1_depth c1_node c1_sign) ↔ ((shared_expr_Classification044_51 c0_depth c0_node c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign)) := (iff_congr (normalization_5090 c0_depth c0_node c1_depth c1_node c1_sign) (normalization_5092 c0_depth c0_node c1_depth c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2402 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1489 c0_depth c0_node c1_depth c1_node c1_sign) := by
  classical
  have ht := (normalized_1251 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((shared_expr_Classification044_48 c0_node c1_node) ∨ (shared_expr_Classification044_44 c0_node c1_node c1_sign)))
  have hn := ht
  exact Iff.mpr (normalization_5093 c0_depth c0_node c1_depth c1_node c1_sign) hn

abbrev shared_expr_Classification044_55 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ∨ (formula_1465 c0_node c1_node c1_sign)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ∨ (formula_1441 c0_node c1_node c1_sign)))
abbrev formula_1490 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_55 c0_depth c0_node c1_depth c1_node c1_sign)

theorem normalized_1252 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_56 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification044_47 c0_node c1_node c1_sign)) ↔ (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_5094 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1490 c0_depth c0_node c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_56 c0_depth c0_node c1_depth c1_node c1_sign) := (iff_congr (normalization_4960 c0_depth c0_node c1_depth c1_node c1_sign) (normalization_5092 c0_depth c0_node c1_depth c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2403 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1490 c0_depth c0_node c1_depth c1_node c1_sign) := by
  classical
  have ht := (normalized_1252 ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification044_47 c0_node c1_node c1_sign)) (shared_expr_Classification044_51 c0_depth c0_node c1_depth c1_node c1_sign) (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign))
  have n0 : (shared_expr_Classification044_52 c0_depth c0_node c1_depth c1_node c1_sign) := by
    exact Iff.mp (normalization_5091 c0_depth c0_node c1_depth c1_node c1_sign) (replay_2401 c0_depth c0_node c1_depth c1_node c1_sign)
  have n1 : ((shared_expr_Classification044_51 c0_depth c0_node c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign)) := by
    exact Iff.mp (normalization_5093 c0_depth c0_node c1_depth c1_node c1_sign) (replay_2402 c0_depth c0_node c1_depth c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5094 c0_depth c0_node c1_depth c1_node c1_sign) hn

abbrev shared_expr_Classification044_57 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ∨ (formula_1441 c0_node c1_node c1_sign)))
abbrev shared_expr_Classification044_58 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))))) ∧ (formula_1442 c0_node c0_sign c1_node)) ∨ (shared_expr_Classification044_57 c0_depth c0_node c1_depth c1_node c1_sign))
abbrev formula_1491 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_58 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

theorem normalized_1253 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_59 (c0_depth c0_node c0_sign c1_depth c1_node : Int) : Prop := ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))))) ∧ ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node)))
abbrev shared_expr_Classification044_60 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))))) ∧ (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_5095 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1491 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ ((shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node) ∨ (shared_expr_Classification044_60 c0_depth c0_node c1_depth c1_node c1_sign)) := (or_congr (and_congr (normalization_5047 c0_depth c1_depth) (normalization_5060 c0_node c0_sign c1_node)) (and_congr (not_congr (normalization_5047 c0_depth c1_depth)) (normalization_5092 c0_depth c0_node c1_depth c1_node c1_sign)))

abbrev shared_expr_Classification044_61 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification044_47 c0_node c1_node c1_sign)))
abbrev shared_expr_Classification044_62 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification044_28 c0_node c0_sign c1_node)) ∨ (shared_expr_Classification044_61 c0_depth c0_node c1_depth c1_node c1_sign))
abbrev shared_expr_Classification044_63 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_62 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ ((shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node) ∨ (shared_expr_Classification044_60 c0_depth c0_node c1_depth c1_node c1_sign)))
theorem normalization_5096 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1466 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1491 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (shared_expr_Classification044_63 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (iff_congr (normalization_4961 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (normalization_5095 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

-- Checked replay of monotonicity.
theorem replay_2404 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1466 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1491 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
  classical
  have ht := (normalized_1253 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) (shared_expr_Classification044_28 c0_node c0_sign c1_node) ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node)) ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification044_47 c0_node c1_node c1_sign)) (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign))
  have n0 : (shared_expr_Classification044_18 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5049 c0_depth c1_depth) (replay_2382 c0_depth c1_depth)
  have n1 : ((shared_expr_Classification044_28 c0_node c0_sign c1_node) ↔ ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node))) := by
    exact Iff.mp (normalization_5062 c0_node c0_sign c1_node) (replay_2388 c0_node c0_sign c1_node)
  have n2 : (shared_expr_Classification044_56 c0_depth c0_node c1_depth c1_node c1_sign) := by
    exact Iff.mp (normalization_5094 c0_depth c0_node c1_depth c1_node c1_sign) (replay_2403 c0_depth c0_node c1_depth c1_node c1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5096 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) hn

theorem normalized_1254 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_64 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_5097 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1443 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)) := (or_congr (and_congr (normalization_5046 c0_depth c1_depth) (normalization_5092 c0_depth c0_node c1_depth c1_node c1_sign)) (and_congr (not_congr (normalization_5046 c0_depth c1_depth)) (normalization_5060 c0_node c0_sign c1_node)))

abbrev shared_expr_Classification044_65 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node) ∨ (shared_expr_Classification044_60 c0_depth c0_node c1_depth c1_node c1_sign)) ↔ ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)))
theorem normalization_5098 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1491 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1443 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (shared_expr_Classification044_65 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (iff_congr (normalization_5095 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (normalization_5097 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2405 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1491 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1443 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
  classical
  have ht := (normalized_1254 ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ((shared_expr_Classification044_29 c0_node c1_node) ∨ (shared_expr_Classification044_25 c0_node c0_sign c1_node)) (shared_expr_Classification044_54 c0_depth c0_node c1_depth c1_node c1_sign))
  have hn := ht
  exact Iff.mpr (normalization_5098 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) hn

theorem normalized_1255 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_66 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_62 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)))
theorem normalization_5099 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1466 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1443 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (shared_expr_Classification044_66 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (iff_congr (normalization_4961 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (normalization_5097 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2406 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1466 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1443 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
  classical
  have ht := (normalized_1255 (shared_expr_Classification044_62 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ((shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node) ∨ (shared_expr_Classification044_60 c0_depth c0_node c1_depth c1_node c1_sign)) ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)))
  have n0 : (shared_expr_Classification044_63 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := by
    exact Iff.mp (normalization_5096 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (replay_2404 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)
  have n1 : (shared_expr_Classification044_65 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := by
    exact Iff.mp (normalization_5098 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (replay_2405 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5099 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) hn

abbrev shared_expr_Classification044_67 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ∧ (formula_1444 c0_node c0_sign c1_node c1_sign)) ∨ ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) ∧ (formula_1443 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1492 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_67 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

theorem normalized_1256 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_68 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))))) ∧ ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)))
abbrev shared_expr_Classification044_69 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign)) ∨ (shared_expr_Classification044_68 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
theorem normalization_5100 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1492 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_69 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5010 c0_depth c1_depth) (normalization_5037 c0_node c0_sign c1_node c1_sign)) (and_congr (not_congr (normalization_5010 c0_depth c1_depth)) (normalization_5097 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

abbrev shared_expr_Classification044_70 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification044_62 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
abbrev shared_expr_Classification044_71 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification044_13 c0_node c0_sign c1_node c1_sign)) ∨ (shared_expr_Classification044_70 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
theorem normalization_5101 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1492 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ ((shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_69 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (iff_congr (normalization_4962 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (normalization_5100 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

-- Checked replay of monotonicity.
abbrev shared_expr_Classification044_72 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))))
theorem replay_2407 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1492 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
  classical
  have ht := (normalized_1256 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) (shared_expr_Classification044_13 c0_node c0_sign c1_node c1_sign) (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign) (shared_expr_Classification044_62 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)))
  have n0 : (shared_expr_Classification044_72 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5013 c0_depth c1_depth) (replay_2366 c0_depth c1_depth)
  have n1 : ((shared_expr_Classification044_13 c0_node c0_sign c1_node c1_sign) ↔ (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign)) := by
    exact Iff.mp (normalization_5039 c0_node c0_sign c1_node c1_sign) (replay_2379 c0_node c0_sign c1_node c1_sign)
  have n2 : (shared_expr_Classification044_66 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := by
    exact Iff.mp (normalization_5099 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (replay_2406 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5101 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) hn

theorem normalized_1257 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_73 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)))
abbrev shared_expr_Classification044_74 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_73 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign)))
theorem normalization_5102 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_5009 c0_depth c1_depth) (normalization_5097 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) (and_congr (not_congr (normalization_5009 c0_depth c1_depth)) (normalization_5037 c0_node c0_sign c1_node c1_sign)))

theorem normalization_5103 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1492 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ ((shared_expr_Classification044_69 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (iff_congr (normalization_5100 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (normalization_5102 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2408 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1492 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
  classical
  have ht := (normalized_1257 ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) (shared_expr_Classification044_14 c0_node c0_sign c1_node c1_sign) ((shared_expr_Classification044_64 c0_depth c0_node c1_depth c1_node c1_sign) ∨ (shared_expr_Classification044_59 c0_depth c0_node c0_sign c1_depth c1_node)))
  have hn := ht
  exact Iff.mpr (normalization_5103 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) hn

theorem normalized_1258 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5104 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ ((shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (iff_congr (normalization_4962 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (normalization_5102 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2409 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : ((formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
  classical
  have ht := (normalized_1258 (shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (shared_expr_Classification044_69 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
  have n0 : ((shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_69 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
    exact Iff.mp (normalization_5101 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (replay_2407 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)
  have n1 : ((shared_expr_Classification044_69 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
    exact Iff.mp (normalization_5103 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (replay_2408 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5104 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) hn

abbrev shared_expr_Classification044_75 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ (c1_kind = (2 : Int))) ∧ (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))) ∧ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1493 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_75 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

theorem normalized_1259 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∧ p2) ↔ (p1 ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5105 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))) ∧ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (and_congr (normalization_1615 c1_kind) (normalization_5102 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

abbrev shared_expr_Classification044_76 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
theorem normalization_5106 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1493 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_76 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (iff_congr (normalization_4963 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (normalization_5105 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

-- Checked replay of monotonicity.
theorem replay_2410 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1493 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
  classical
  have ht := (normalized_1259 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) (shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
  have n0 : ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_4996 c1_kind) (replay_2359 c1_kind)
  have n1 : ((shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := by
    exact Iff.mp (normalization_5104 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) (replay_2409 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5106 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) hn

abbrev shared_expr_Classification044_77 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))) ∧ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (¬ ((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∨ (¬ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1494 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_77 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

theorem normalized_1260 (p0 p1 : Prop) : ((p0 ∧ p1) ↔ (¬ ((¬ p0) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5107 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (¬ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (not_congr (normalization_5102 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

theorem normalization_5108 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : ((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∨ (¬ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))) ↔ ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))) := (or_congr (normalization_1616 c1_kind) (normalization_5107 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

theorem normalization_5109 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (¬ ((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∨ (¬ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) ↔ (¬ ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) := (not_congr (normalization_5108 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

abbrev shared_expr_Classification044_78 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (¬ ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
theorem normalization_5110 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1494 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_78 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (iff_congr (normalization_5105 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (normalization_5109 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2411 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1494 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
  classical
  have ht := (normalized_1260 ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
  have hn := ht
  exact Iff.mpr (normalization_5110 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) hn

abbrev shared_expr_Classification044_79 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ (c1_kind = (2 : Int))) ∧ (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (¬ ((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∨ (¬ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1495 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_79 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

theorem normalized_1261 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_80 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ (¬ ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
theorem normalization_5111 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1495 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_80 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (iff_congr (normalization_4963 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (normalization_5109 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2412 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1495 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
  classical
  have ht := (normalized_1261 ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) (((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))))
  have n0 : (shared_expr_Classification044_76 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
    exact Iff.mp (normalization_5106 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (replay_2410 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)
  have n1 : (shared_expr_Classification044_78 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
    exact Iff.mp (normalization_5110 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (replay_2411 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5111 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) hn

abbrev shared_expr_Classification044_81 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ∧ (¬ ((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∨ (¬ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev shared_expr_Classification044_82 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) ∨ (shared_expr_Classification044_81 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
abbrev formula_1496 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_82 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Classification044_83 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) ↔ (formula_1496 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
abbrev formula_1497 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_83 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

theorem normalized_1262 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_84 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) ∧ (¬ ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev shared_expr_Classification044_85 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) ∨ (shared_expr_Classification044_84 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_5112 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1496 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_85 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_3540 c0_kind) (normalization_4990 c1_kind)) (and_congr (not_congr (normalization_3540 c0_kind)) (normalization_5109 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Classification044_86 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev shared_expr_Classification044_87 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) ∨ (shared_expr_Classification044_86 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
abbrev shared_expr_Classification044_88 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_87 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_85 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_5113 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1497 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_88 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (iff_congr (normalization_4964 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (normalization_5112 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

-- Checked replay of monotonicity.
theorem replay_2413 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1497 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
  classical
  have ht := (normalized_1262 (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))) ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification044_71 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))))
  have n0 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3542 c0_kind) (replay_1299 c0_kind)
  have n1 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_4992 c1_kind) (replay_2356 c1_kind)
  have n2 : (shared_expr_Classification044_80 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
    exact Iff.mp (normalization_5111 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (replay_2412 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_5113 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) hn

theorem normalized_1263 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_89 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ (¬ ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev shared_expr_Classification044_90 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_89 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ∨ ((¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))))
theorem normalization_5114 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1446 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_90 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_3539 c0_kind) (normalization_5109 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) (and_congr (not_congr (normalization_3539 c0_kind)) (normalization_4990 c1_kind)))

abbrev shared_expr_Classification044_91 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_85 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_90 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_5115 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : ((formula_1496 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (formula_1446 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) ↔ (shared_expr_Classification044_91 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (iff_congr (normalization_5112 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (normalization_5114 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2414 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : ((formula_1496 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (formula_1446 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) := by
  classical
  have ht := (normalized_1263 ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))) ((¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) ∨ (¬ (shared_expr_Classification044_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))))
  have hn := ht
  exact Iff.mpr (normalization_5115 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) hn

abbrev shared_expr_Classification044_92 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) ↔ (formula_1446 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
abbrev formula_1498 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification044_92 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

theorem normalized_1264 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification044_93 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((shared_expr_Classification044_87 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_90 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_5116 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1498 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification044_93 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (iff_congr (normalization_4964 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (normalization_5114 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

-- Checked replay of trans.
theorem replay_2415 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1498 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
  classical
  have ht := (normalized_1264 (shared_expr_Classification044_87 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (shared_expr_Classification044_85 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (shared_expr_Classification044_90 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
  have n0 : (shared_expr_Classification044_88 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
    exact Iff.mp (normalization_5113 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (replay_2413 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)
  have n1 : (shared_expr_Classification044_91 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := by
    exact Iff.mp (normalization_5115 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) (replay_2414 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5116 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) hn

end H4Formal.Generated.Classification
