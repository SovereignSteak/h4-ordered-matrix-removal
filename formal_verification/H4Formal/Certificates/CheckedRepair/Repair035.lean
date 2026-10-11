import H4Formal.Certificates.CheckedRepair.Repair034

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_745 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3048 (c2_kind : Int) : ((¬ (c2_kind = (0 : Int))) ↔ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ↔ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_2977 c2_kind) (normalization_1002 c2_kind))

-- Checked replay of trans.
theorem replay_2144 (c2_kind : Int) : ((¬ (c2_kind = (0 : Int))) ↔ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_745 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))
  have n0 : ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))))) := by
    exact Iff.mp (normalization_3046 c2_kind) (replay_2142 c2_kind)
  have n1 : ((¬ (¬ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_3047 c2_kind) (replay_2143 c2_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3048 c2_kind) hn

abbrev shared_expr_Repair035_0 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_813 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) ↔ ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_822 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (shared_expr_Repair035_0 c0_group c0_level c0_mode c2_group c2_level c2_mode)

theorem normalized_746 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3049 (c0_level c2_level : Int) : ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_3050 (c0_level c2_level : Int) : (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := (not_congr (normalization_3049 c0_level c2_level))

theorem normalization_3051 (c0_level c2_level : Int) : ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ↔ ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) := (or_congr (normalization_3050 c0_level c2_level) (normalization_3019 c0_level c2_level))

theorem normalization_3052 (c0_mode c2_mode : Int) : ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_3053 (c0_mode c2_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) := (not_congr (normalization_3052 c0_mode c2_mode))

theorem normalization_3054 (c0_mode c2_mode : Int) : ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_3053 c0_mode c2_mode) (normalization_3016 c0_mode c2_mode))

abbrev shared_expr_Repair035_1 (c0_group c0_mode c2_group c2_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))))
theorem normalization_3055 (c0_group c0_mode c2_group c2_mode : Int) : (formula_632 c0_group c0_mode c2_group c2_mode) ↔ (shared_expr_Repair035_1 c0_group c0_mode c2_group c2_mode) := (or_congr (and_congr (normalization_3054 c0_mode c2_mode) (normalization_3016 c0_mode c2_mode)) (and_congr (not_congr (normalization_3054 c0_mode c2_mode)) (normalization_3014 c0_group c2_group)))

abbrev shared_expr_Repair035_2 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair035_1 c0_group c0_mode c2_group c2_mode)))
theorem normalization_3056 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair035_2 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_3051 c0_level c2_level) (normalization_3019 c0_level c2_level)) (and_congr (not_congr (normalization_3051 c0_level c2_level)) (normalization_3055 c0_group c0_mode c2_group c2_mode)))

abbrev shared_expr_Repair035_3 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair035_2 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_3057 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) ↔ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode) := (or_congr (and_congr (normalization_2978 c0_mode c2_mode) (normalization_3056 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (and_congr (not_congr (normalization_2978 c0_mode c2_mode)) (normalization_693 c0_mode)))

abbrev shared_expr_Repair035_4 (c0_group c0_mode c2_group c2_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair035_5 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair035_4 c0_group c0_mode c2_group c2_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int))))))
abbrev shared_expr_Repair035_6 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair035_5 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_3058 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_822 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ ((shared_expr_Repair035_6 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (iff_congr (normalization_3021 c0_group c0_level c0_mode c2_group c2_level c2_mode) (normalization_3057 c0_group c0_level c0_mode c2_group c2_level c2_mode))

-- Checked replay of rewrite.
theorem replay_2145 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : (formula_822 c0_group c0_level c0_mode c2_group c2_level c2_mode) := by
  classical
  have ht := (normalized_746 ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c2_mode) ≤ (3 : Int)))) ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c2_group)) ≤ (-1 : Int)) ((c0_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3058 c0_group c0_level c0_mode c2_group c2_level c2_mode) hn

abbrev shared_expr_Repair035_7 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_823 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (shared_expr_Repair035_7 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)

theorem normalized_747 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3059 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_823 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (or_congr (normalization_1002 c2_kind) (normalization_3057 c0_group c0_level c0_mode c2_group c2_level c2_mode))

abbrev shared_expr_Repair035_8 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_6 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem normalization_3060 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_814 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_823 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Repair035_8 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_3022 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (normalization_3059 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of monotonicity.
theorem replay_2146 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_814 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_823 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_747 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) (shared_expr_Repair035_6 c0_group c0_level c0_mode c2_group c2_level c2_mode) (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode))
  have n0 : ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_3048 c2_kind) (replay_2144 c2_kind)
  have n1 : ((shared_expr_Repair035_6 c0_group c0_level c0_mode c2_group c2_level c2_mode) ↔ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := by
    exact Iff.mp (normalization_3058 c0_group c0_level c0_mode c2_group c2_level c2_mode) (replay_2145 c0_group c0_level c0_mode c2_group c2_level c2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3060 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_748 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3061 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : (formula_797 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := (or_congr (normalization_79 c2_kind) (or_congr (normalization_81 c2_kind) (normalization_3057 c0_group c0_level c0_mode c2_group c2_level c2_mode)))

abbrev shared_expr_Repair035_9 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := ((((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem normalization_3062 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_823 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_797 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Repair035_9 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_3059 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (normalization_3061 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of rewrite.
theorem replay_2147 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_823 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_797 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_748 ((c2_kind) ≤ (0 : Int)) ((c2_kind) ≤ (-1 : Int)) (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode))
  have hn := ht
  exact Iff.mpr (normalization_3062 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_749 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair035_10 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : Prop := (((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_6 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ↔ ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
theorem normalization_3063 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_814 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_797 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) ↔ (shared_expr_Repair035_10 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := (iff_congr (normalization_3022 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (normalization_3061 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode))

-- Checked replay of trans.
theorem replay_2148 (c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode : Int) : ((formula_814 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) ↔ (formula_797 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)) := by
  classical
  have ht := (normalized_749 ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_6 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ((¬ ((c2_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Repair035_3 c0_group c0_level c0_mode c2_group c2_level c2_mode)))
  have n0 : (shared_expr_Repair035_8 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_3060 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (replay_2146 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)
  have n1 : (shared_expr_Repair035_9 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) := by
    exact Iff.mp (normalization_3062 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) (replay_2147 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3063 c0_group c0_level c0_mode c2_group c2_kind c2_level c2_mode) hn

theorem normalized_750 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3064 (c0_kind : Int) : ((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int))) ↔ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) := (and_congr (normalization_476 c0_kind) (normalization_478 c0_kind))

theorem normalization_3065 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ ((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int)))) ↔ ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) := (iff_congr (normalization_141 c0_kind) (normalization_3064 c0_kind))

-- Checked replay of rewrite.
theorem replay_2149 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ ((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_750 (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3065 c0_kind) hn

theorem normalized_751 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3066 (c0_kind : Int) : (((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ↔ ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_3064 c0_kind) (normalization_481 c0_kind))

-- Checked replay of rewrite.
theorem replay_2150 (c0_kind : Int) : (((c0_kind ≤ (2 : Int)) ∧ (c0_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_751 ((c0_kind) ≤ (2 : Int)) ((c0_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3066 c0_kind) hn

theorem normalized_752 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3067 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) ↔ ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_141 c0_kind) (normalization_481 c0_kind))

-- Checked replay of trans.
theorem replay_2151 (c0_kind : Int) : ((c0_kind = (2 : Int)) ↔ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_752 (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))))
  have n0 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_3065 c0_kind) (replay_2149 c0_kind)
  have n1 : ((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c0_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3066 c0_kind) (replay_2150 c0_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3067 c0_kind) hn

theorem normalized_753 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3068 (c2_kind : Int) : ((c2_kind ≤ (1 : Int)) ∧ (c2_kind ≥ (1 : Int))) ↔ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) := (and_congr (normalization_100 c2_kind) (normalization_102 c2_kind))

theorem normalization_3069 (c2_kind : Int) : ((c2_kind = (1 : Int)) ↔ ((c2_kind ≤ (1 : Int)) ∧ (c2_kind ≥ (1 : Int)))) ↔ ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) := (iff_congr (normalization_16 c2_kind) (normalization_3068 c2_kind))

-- Checked replay of rewrite.
theorem replay_2152 (c2_kind : Int) : ((c2_kind = (1 : Int)) ↔ ((c2_kind ≤ (1 : Int)) ∧ (c2_kind ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_753 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3069 c2_kind) hn

theorem normalized_754 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3070 (c2_kind : Int) : ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))) ↔ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))) := (or_congr (normalization_101 c2_kind) (normalization_103 c2_kind))

theorem normalization_3071 (c2_kind : Int) : (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int))))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int)))))) := (not_congr (normalization_3070 c2_kind))

theorem normalization_3072 (c2_kind : Int) : (((c2_kind ≤ (1 : Int)) ∧ (c2_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))))) ↔ ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_3068 c2_kind) (normalization_3071 c2_kind))

-- Checked replay of rewrite.
theorem replay_2153 (c2_kind : Int) : (((c2_kind ≤ (1 : Int)) ∧ (c2_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_754 ((c2_kind) ≤ (1 : Int)) ((c2_kind) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3072 c2_kind) hn

theorem normalized_755 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3073 (c2_kind : Int) : ((c2_kind = (1 : Int)) ↔ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))))) ↔ ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_16 c2_kind) (normalization_3071 c2_kind))

-- Checked replay of trans.
theorem replay_2154 (c2_kind : Int) : ((c2_kind = (1 : Int)) ↔ (¬ ((¬ (c2_kind ≤ (1 : Int))) ∨ (¬ (c2_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_755 (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))))
  have n0 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_3069 c2_kind) (replay_2152 c2_kind)
  have n1 : ((((c2_kind) ≤ (1 : Int)) ∧ (¬ ((c2_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3072 c2_kind) (replay_2153 c2_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3073 c2_kind) hn

theorem normalized_756 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3074 (c2_kind : Int) : ((c2_kind ≤ (2 : Int)) ∧ (c2_kind ≥ (2 : Int))) ↔ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) := (and_congr (normalization_51 c2_kind) (normalization_53 c2_kind))

theorem normalization_3075 (c2_kind : Int) : ((c2_kind = (2 : Int)) ↔ ((c2_kind ≤ (2 : Int)) ∧ (c2_kind ≥ (2 : Int)))) ↔ ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) := (iff_congr (normalization_34 c2_kind) (normalization_3074 c2_kind))

-- Checked replay of rewrite.
theorem replay_2155 (c2_kind : Int) : ((c2_kind = (2 : Int)) ↔ ((c2_kind ≤ (2 : Int)) ∧ (c2_kind ≥ (2 : Int)))) := by
  classical
  have ht := (normalized_756 (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3075 c2_kind) hn

theorem normalized_757 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3076 (c2_kind : Int) : (((c2_kind ≤ (2 : Int)) ∧ (c2_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ↔ ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_3074 c2_kind) (normalization_1076 c2_kind))

-- Checked replay of rewrite.
theorem replay_2156 (c2_kind : Int) : (((c2_kind ≤ (2 : Int)) ∧ (c2_kind ≥ (2 : Int))) ↔ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_757 ((c2_kind) ≤ (2 : Int)) ((c2_kind) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3076 c2_kind) hn

theorem normalized_758 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3077 (c2_kind : Int) : ((c2_kind = (2 : Int)) ↔ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ↔ ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := (iff_congr (normalization_34 c2_kind) (normalization_1076 c2_kind))

-- Checked replay of trans.
theorem replay_2157 (c2_kind : Int) : ((c2_kind = (2 : Int)) ↔ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) := by
  classical
  have ht := (normalized_758 (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))))
  have n0 : ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) := by
    exact Iff.mp (normalization_3075 c2_kind) (replay_2155 c2_kind)
  have n1 : ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3076 c2_kind) (replay_2156 c2_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3077 c2_kind) hn

theorem normalized_759 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3078 (c2_kind : Int) : (¬ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ↔ (¬ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := (not_congr (normalization_1076 c2_kind))

theorem normalization_3079 (c2_kind : Int) : ((¬ (c2_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))) ↔ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))))) := (iff_congr (normalization_2991 c2_kind) (normalization_3078 c2_kind))

-- Checked replay of monotonicity.
theorem replay_2158 (c2_kind : Int) : ((¬ (c2_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_759 (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))
  have n0 : ((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_3077 c2_kind) (replay_2157 c2_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_3079 c2_kind) hn

theorem normalized_760 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3080 (c2_kind : Int) : ((¬ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ↔ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ↔ ((¬ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_3078 c2_kind) (normalization_1075 c2_kind))

-- Checked replay of rewrite.
theorem replay_2159 (c2_kind : Int) : ((¬ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ↔ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_760 ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_3080 c2_kind) hn

theorem normalized_761 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3081 (c2_kind : Int) : ((¬ (c2_kind = (2 : Int))) ↔ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ↔ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ↔ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_2991 c2_kind) (normalization_1075 c2_kind))

-- Checked replay of trans.
theorem replay_2160 (c2_kind : Int) : ((¬ (c2_kind = (2 : Int))) ↔ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_761 (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))
  have n0 : ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_3079 c2_kind) (replay_2158 c2_kind)
  have n1 : ((¬ (¬ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c2_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c2_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_3080 c2_kind) (replay_2159 c2_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3081 c2_kind) hn

theorem normalized_762 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3082 (c0_depth c2_depth : Int) : (c0_depth ≤ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_3083 (c0_depth c2_depth : Int) : (c0_depth ≥ c2_depth) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3084 (c0_depth c2_depth : Int) : ((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_3082 c0_depth c2_depth) (normalization_3083 c0_depth c2_depth))

abbrev shared_expr_Repair035_11 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
theorem normalization_3085 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ ((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth))) ↔ (shared_expr_Repair035_11 c0_depth c2_depth) := (iff_congr (normalization_2957 c0_depth c2_depth) (normalization_3084 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2161 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ ((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth))) := by
  classical
  have ht := (normalized_762 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3085 c0_depth c2_depth) hn

theorem normalized_763 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3086 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_3087 (c0_depth c2_depth : Int) : ((c0_depth ≤ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := (iff_congr (normalization_3082 c0_depth c2_depth) (normalization_3086 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2162 (c0_depth c2_depth : Int) : ((c0_depth ≤ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_763 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3087 c0_depth c2_depth) hn

theorem normalized_764 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3088 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3089 (c0_depth c2_depth : Int) : ((c0_depth ≥ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_3083 c0_depth c2_depth) (normalization_3088 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2163 (c0_depth c2_depth : Int) : ((c0_depth ≥ c2_depth) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_764 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3089 c0_depth c2_depth) hn

theorem normalized_765 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3090 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_3086 c0_depth c2_depth) (normalization_3088 c0_depth c2_depth))

theorem normalization_3091 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Repair035_11 c0_depth c2_depth) := (iff_congr (normalization_3084 c0_depth c2_depth) (normalization_3090 c0_depth c2_depth))

-- Checked replay of monotonicity.
theorem replay_2164 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_765 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))
  have n0 : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3087 c0_depth c2_depth) (replay_2162 c0_depth c2_depth)
  have n1 : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3089 c0_depth c2_depth) (replay_2163 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3091 c0_depth c2_depth) hn

abbrev shared_expr_Repair035_12 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))))
abbrev formula_824 (c0_depth c2_depth : Int) : Prop := (shared_expr_Repair035_12 c0_depth c2_depth)

theorem normalized_766 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3092 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := (not_congr (normalization_3086 c0_depth c2_depth))

theorem normalization_3093 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_3088 c0_depth c2_depth))

theorem normalization_3094 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_3092 c0_depth c2_depth) (normalization_3093 c0_depth c2_depth))

theorem normalization_3095 (c0_depth c2_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_3094 c0_depth c2_depth))

abbrev shared_expr_Repair035_13 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))))))
theorem normalization_3096 (c0_depth c2_depth : Int) : (formula_824 c0_depth c2_depth) ↔ (shared_expr_Repair035_13 c0_depth c2_depth) := (iff_congr (normalization_3090 c0_depth c2_depth) (normalization_3095 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2165 (c0_depth c2_depth : Int) : (formula_824 c0_depth c2_depth) := by
  classical
  have ht := (normalized_766 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3096 c0_depth c2_depth) hn

theorem normalized_767 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3097 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair035_13 c0_depth c2_depth) := (iff_congr (normalization_3084 c0_depth c2_depth) (normalization_3095 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_2166 (c0_depth c2_depth : Int) : (((c0_depth ≤ c2_depth) ∧ (c0_depth ≥ c2_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_767 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Repair035_13 c0_depth c2_depth))
  have n0 : (shared_expr_Repair035_11 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3091 c0_depth c2_depth) (replay_2164 c0_depth c2_depth)
  have n1 : (shared_expr_Repair035_13 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3096 c0_depth c2_depth) (replay_2165 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3097 c0_depth c2_depth) hn

theorem normalized_768 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3098 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair035_13 c0_depth c2_depth) := (iff_congr (normalization_2957 c0_depth c2_depth) (normalization_3095 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_2167 (c0_depth c2_depth : Int) : ((c0_depth = c2_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_768 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (shared_expr_Repair035_13 c0_depth c2_depth))
  have n0 : (shared_expr_Repair035_11 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3085 c0_depth c2_depth) (replay_2161 c0_depth c2_depth)
  have n1 : (shared_expr_Repair035_13 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3097 c0_depth c2_depth) (replay_2166 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3098 c0_depth c2_depth) hn

theorem normalized_769 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3099 (c0_node c2_node : Int) : (c0_node ≤ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3100 (c0_node c2_node : Int) : (c0_node ≥ c2_node) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3101 (c0_node c2_node : Int) : ((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_3099 c0_node c2_node) (normalization_3100 c0_node c2_node))

abbrev shared_expr_Repair035_14 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
theorem normalization_3102 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ ((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node))) ↔ (shared_expr_Repair035_14 c0_node c2_node) := (iff_congr (normalization_2958 c0_node c2_node) (normalization_3101 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2168 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ ((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node))) := by
  classical
  have ht := (normalized_769 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3102 c0_node c2_node) hn

theorem normalized_770 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3103 (c0_node c2_node : Int) : ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_3104 (c0_node c2_node : Int) : ((c0_node ≤ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (iff_congr (normalization_3099 c0_node c2_node) (normalization_3103 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2169 (c0_node c2_node : Int) : ((c0_node ≤ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_770 ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3104 c0_node c2_node) hn

theorem normalized_771 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3105 (c0_node c2_node : Int) : ((c0_node ≥ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (iff_congr (normalization_3100 c0_node c2_node) (normalization_3023 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2170 (c0_node c2_node : Int) : ((c0_node ≥ c2_node) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_771 ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3105 c0_node c2_node) hn

theorem normalized_772 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3106 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := (and_congr (normalization_3103 c0_node c2_node) (normalization_3023 c0_node c2_node))

theorem normalization_3107 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ (shared_expr_Repair035_14 c0_node c2_node) := (iff_congr (normalization_3101 c0_node c2_node) (normalization_3106 c0_node c2_node))

-- Checked replay of monotonicity.
theorem replay_2171 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_772 ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)) (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))
  have n0 : (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ↔ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_3104 c0_node c2_node) (replay_2169 c0_node c2_node)
  have n1 : ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_3105 c0_node c2_node) (replay_2170 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3107 c0_node c2_node) hn

abbrev shared_expr_Repair035_15 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))))
abbrev formula_825 (c0_node c2_node : Int) : Prop := (shared_expr_Repair035_15 c0_node c2_node)

theorem normalized_773 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3108 (c0_node c2_node : Int) : (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ↔ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_3103 c0_node c2_node))

theorem normalization_3109 (c0_node c2_node : Int) : ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) ↔ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) := (or_congr (normalization_3108 c0_node c2_node) (normalization_3024 c0_node c2_node))

theorem normalization_3110 (c0_node c2_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_3109 c0_node c2_node))

abbrev shared_expr_Repair035_16 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))))
theorem normalization_3111 (c0_node c2_node : Int) : (formula_825 c0_node c2_node) ↔ (shared_expr_Repair035_16 c0_node c2_node) := (iff_congr (normalization_3106 c0_node c2_node) (normalization_3110 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2172 (c0_node c2_node : Int) : (formula_825 c0_node c2_node) := by
  classical
  have ht := (normalized_773 ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3111 c0_node c2_node) hn

theorem normalized_774 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3112 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair035_16 c0_node c2_node) := (iff_congr (normalization_3101 c0_node c2_node) (normalization_3110 c0_node c2_node))

-- Checked replay of trans.
theorem replay_2173 (c0_node c2_node : Int) : (((c0_node ≤ c2_node) ∧ (c0_node ≥ c2_node)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_774 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) (shared_expr_Repair035_16 c0_node c2_node))
  have n0 : (shared_expr_Repair035_14 c0_node c2_node) := by
    exact Iff.mp (normalization_3107 c0_node c2_node) (replay_2171 c0_node c2_node)
  have n1 : (shared_expr_Repair035_16 c0_node c2_node) := by
    exact Iff.mp (normalization_3111 c0_node c2_node) (replay_2172 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3112 c0_node c2_node) hn

theorem normalized_775 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3113 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ↔ (shared_expr_Repair035_16 c0_node c2_node) := (iff_congr (normalization_2958 c0_node c2_node) (normalization_3110 c0_node c2_node))

-- Checked replay of trans.
theorem replay_2174 (c0_node c2_node : Int) : ((c0_node = c2_node) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_775 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) (shared_expr_Repair035_16 c0_node c2_node))
  have n0 : (shared_expr_Repair035_14 c0_node c2_node) := by
    exact Iff.mp (normalization_3102 c0_node c2_node) (replay_2168 c0_node c2_node)
  have n1 : (shared_expr_Repair035_16 c0_node c2_node) := by
    exact Iff.mp (normalization_3112 c0_node c2_node) (replay_2173 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3113 c0_node c2_node) hn

theorem normalized_776 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3114 (c0_sign : Int) : ((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int))) ↔ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) := (and_congr (normalization_456 c0_sign) (normalization_458 c0_sign))

theorem normalization_3115 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ ((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int)))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) := (iff_congr (normalization_144 c0_sign) (normalization_3114 c0_sign))

-- Checked replay of rewrite.
theorem replay_2175 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ ((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_776 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3115 c0_sign) hn

theorem normalized_777 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3116 (c0_sign : Int) : (((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_3114 c0_sign) (normalization_461 c0_sign))

-- Checked replay of rewrite.
theorem replay_2176 (c0_sign : Int) : (((c0_sign ≤ (0 : Int)) ∧ (c0_sign ≥ (0 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_777 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3116 c0_sign) hn

theorem normalized_778 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3117 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := (iff_congr (normalization_144 c0_sign) (normalization_461 c0_sign))

-- Checked replay of trans.
theorem replay_2177 (c0_sign : Int) : ((c0_sign = (0 : Int)) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_778 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_3115 c0_sign) (replay_2175 c0_sign)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3116 c0_sign) (replay_2176 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3117 c0_sign) hn

theorem normalized_779 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3118 (c2_sign : Int) : ((c2_sign ≤ (1 : Int)) ∧ (c2_sign ≥ (1 : Int))) ↔ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) := (and_congr (normalization_114 c2_sign) (normalization_116 c2_sign))

theorem normalization_3119 (c2_sign : Int) : ((c2_sign = (1 : Int)) ↔ ((c2_sign ≤ (1 : Int)) ∧ (c2_sign ≥ (1 : Int)))) ↔ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) := (iff_congr (normalization_26 c2_sign) (normalization_3118 c2_sign))

-- Checked replay of rewrite.
theorem replay_2178 (c2_sign : Int) : ((c2_sign = (1 : Int)) ↔ ((c2_sign ≤ (1 : Int)) ∧ (c2_sign ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_779 (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3119 c2_sign) hn

theorem normalized_780 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3120 (c2_sign : Int) : (((c2_sign ≤ (1 : Int)) ∧ (c2_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_3118 c2_sign) (normalization_119 c2_sign))

-- Checked replay of rewrite.
theorem replay_2179 (c2_sign : Int) : (((c2_sign ≤ (1 : Int)) ∧ (c2_sign ≥ (1 : Int))) ↔ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_780 ((c2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3120 c2_sign) hn

theorem normalized_781 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3121 (c2_sign : Int) : ((c2_sign = (1 : Int)) ↔ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := (iff_congr (normalization_26 c2_sign) (normalization_119 c2_sign))

-- Checked replay of trans.
theorem replay_2180 (c2_sign : Int) : ((c2_sign = (1 : Int)) ↔ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_781 (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))))
  have n0 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_3119 c2_sign) (replay_2178 c2_sign)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3120 c2_sign) (replay_2179 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3121 c2_sign) hn

theorem normalized_782 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ (¬ p3)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3122 (c0_sign c2_sign : Int) : ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := (and_congr (normalization_461 c0_sign) (normalization_119 c2_sign))

abbrev shared_expr_Repair035_17 (c0_sign c2_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ↔ ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))))
theorem normalization_3123 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) ↔ (shared_expr_Repair035_17 c0_sign c2_sign) := (iff_congr (normalization_2959 c0_sign c2_sign) (normalization_3122 c0_sign c2_sign))

-- Checked replay of monotonicity.
theorem replay_2181 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) := by
  classical
  have ht := (normalized_782 (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))
  have n0 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3117 c0_sign) (replay_2177 c0_sign)
  have n1 : ((((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_3121 c2_sign) (replay_2180 c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3123 c0_sign c2_sign) hn

abbrev shared_expr_Repair035_18 (c0_sign c2_sign : Int) : Prop := (((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev formula_826 (c0_sign c2_sign : Int) : Prop := (shared_expr_Repair035_18 c0_sign c2_sign)

theorem normalized_783 (p0 p1 p2 p3 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2) ∨ (¬ (¬ p3))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3124 (c0_sign c2_sign : Int) : ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ↔ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) := (or_congr (normalization_457 c0_sign) (or_congr (normalization_459 c0_sign) (or_congr (normalization_115 c2_sign) (normalization_117 c2_sign))))

theorem normalization_3125 (c0_sign c2_sign : Int) : (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))) := (not_congr (normalization_3124 c0_sign c2_sign))

abbrev shared_expr_Repair035_19 (c0_sign c2_sign : Int) : Prop := (((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
theorem normalization_3126 (c0_sign c2_sign : Int) : (formula_826 c0_sign c2_sign) ↔ (shared_expr_Repair035_19 c0_sign c2_sign) := (iff_congr (normalization_3122 c0_sign c2_sign) (normalization_3125 c0_sign c2_sign))

-- Checked replay of rewrite.
theorem replay_2182 (c0_sign c2_sign : Int) : (formula_826 c0_sign c2_sign) := by
  classical
  have ht := (normalized_783 ((c0_sign) ≤ (0 : Int)) ((c0_sign) ≤ (-1 : Int)) ((c2_sign) ≤ (1 : Int)) ((c2_sign) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3126 c0_sign c2_sign) hn

theorem normalized_784 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair035_20 (c0_sign c2_sign : Int) : Prop := (((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
theorem normalization_3127 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) ↔ (shared_expr_Repair035_20 c0_sign c2_sign) := (iff_congr (normalization_2959 c0_sign c2_sign) (normalization_3125 c0_sign c2_sign))

-- Checked replay of trans.
theorem replay_2183 (c0_sign c2_sign : Int) : (((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int))) ↔ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_784 ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ((¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))))
  have n0 : (shared_expr_Repair035_17 c0_sign c2_sign) := by
    exact Iff.mp (normalization_3123 c0_sign c2_sign) (replay_2181 c0_sign c2_sign)
  have n1 : (shared_expr_Repair035_19 c0_sign c2_sign) := by
    exact Iff.mp (normalization_3126 c0_sign c2_sign) (replay_2182 c0_sign c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3127 c0_sign c2_sign) hn

abbrev shared_expr_Repair035_21 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair035_22 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair035_21 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))))
abbrev formula_827 (c0_node c0_sign c2_node c2_sign : Int) : Prop := (shared_expr_Repair035_22 c0_node c0_sign c2_node c2_sign)

abbrev shared_expr_Repair035_23 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (formula_827 c0_node c0_sign c2_node c2_sign))
abbrev formula_828 (c0_node c0_sign c2_node c2_sign : Int) : Prop := (shared_expr_Repair035_23 c0_node c0_sign c2_node c2_sign)

theorem normalized_785 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ (¬ p4)))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ (¬ p4)))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair035_24 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int)))))))
abbrev shared_expr_Repair035_25 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair035_24 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
theorem normalization_3128 (c0_node c0_sign c2_node c2_sign : Int) : (formula_827 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair035_25 c0_node c0_sign c2_node c2_sign) := (or_congr (and_congr (normalization_3110 c0_node c2_node) (normalization_3125 c0_sign c2_sign)) (and_congr (not_congr (normalization_3110 c0_node c2_node)) (normalization_3024 c0_node c2_node)))

abbrev shared_expr_Repair035_26 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair035_27 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((shared_expr_Repair035_26 c0_node c0_sign c2_node c2_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))))
theorem normalization_3129 (c0_node c0_sign c2_node c2_sign : Int) : (formula_828 c0_node c0_sign c2_node c2_sign) ↔ ((shared_expr_Repair035_27 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair035_25 c0_node c0_sign c2_node c2_sign)) := (iff_congr (normalization_3025 c0_node c0_sign c2_node c2_sign) (normalization_3128 c0_node c0_sign c2_node c2_sign))

-- Checked replay of monotonicity.
theorem replay_2184 (c0_node c0_sign c2_node c2_sign : Int) : (formula_828 c0_node c0_sign c2_node c2_sign) := by
  classical
  have ht := (normalized_785 (((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))) ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c2_sign) ≤ (1 : Int)) ∧ (¬ ((c2_sign) ≤ (0 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have n0 : (shared_expr_Repair035_16 c0_node c2_node) := by
    exact Iff.mp (normalization_3113 c0_node c2_node) (replay_2174 c0_node c2_node)
  have n1 : (shared_expr_Repair035_20 c0_sign c2_sign) := by
    exact Iff.mp (normalization_3127 c0_sign c2_sign) (replay_2183 c0_sign c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3129 c0_node c0_sign c2_node c2_sign) hn

theorem normalized_786 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ (¬ p2)))) ↔ ((p0 ∧ (¬ (¬ p2))) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair035_28 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_24 c0_node c0_sign c2_node c2_sign))
theorem normalization_3130 (c0_node c0_sign c2_node c2_sign : Int) : (formula_794 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair035_28 c0_node c0_sign c2_node c2_sign) := (or_congr (and_congr (normalization_3109 c0_node c2_node) (normalization_3024 c0_node c2_node)) (and_congr (not_congr (normalization_3109 c0_node c2_node)) (normalization_3125 c0_sign c2_sign)))

theorem normalization_3131 (c0_node c0_sign c2_node c2_sign : Int) : ((formula_827 c0_node c0_sign c2_node c2_sign) ↔ (formula_794 c0_node c0_sign c2_node c2_sign)) ↔ ((shared_expr_Repair035_25 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair035_28 c0_node c0_sign c2_node c2_sign)) := (iff_congr (normalization_3128 c0_node c0_sign c2_node c2_sign) (normalization_3130 c0_node c0_sign c2_node c2_sign))

-- Checked replay of rewrite.
theorem replay_2185 (c0_node c0_sign c2_node c2_sign : Int) : ((formula_827 c0_node c0_sign c2_node c2_sign) ↔ (formula_794 c0_node c0_sign c2_node c2_sign)) := by
  classical
  have ht := (normalized_786 ((¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int))))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c2_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c2_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3131 c0_node c0_sign c2_node c2_sign) hn

abbrev shared_expr_Repair035_29 (c0_node c0_sign c2_node c2_sign : Int) : Prop := ((((c0_node = c2_node) ∧ ((c0_sign = (0 : Int)) ∧ (c2_sign = (1 : Int)))) ∨ ((¬ (c0_node = c2_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))))) ↔ (formula_794 c0_node c0_sign c2_node c2_sign))
abbrev formula_829 (c0_node c0_sign c2_node c2_sign : Int) : Prop := (shared_expr_Repair035_29 c0_node c0_sign c2_node c2_sign)

theorem normalized_787 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3132 (c0_node c0_sign c2_node c2_sign : Int) : (formula_829 c0_node c0_sign c2_node c2_sign) ↔ ((shared_expr_Repair035_27 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair035_28 c0_node c0_sign c2_node c2_sign)) := (iff_congr (normalization_3025 c0_node c0_sign c2_node c2_sign) (normalization_3130 c0_node c0_sign c2_node c2_sign))

-- Checked replay of trans.
theorem replay_2186 (c0_node c0_sign c2_node c2_sign : Int) : (formula_829 c0_node c0_sign c2_node c2_sign) := by
  classical
  have ht := (normalized_787 (shared_expr_Repair035_27 c0_node c0_sign c2_node c2_sign) (shared_expr_Repair035_25 c0_node c0_sign c2_node c2_sign) (shared_expr_Repair035_28 c0_node c0_sign c2_node c2_sign))
  have n0 : ((shared_expr_Repair035_27 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair035_25 c0_node c0_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_3129 c0_node c0_sign c2_node c2_sign) (replay_2184 c0_node c0_sign c2_node c2_sign)
  have n1 : ((shared_expr_Repair035_25 c0_node c0_sign c2_node c2_sign) ↔ (shared_expr_Repair035_28 c0_node c0_sign c2_node c2_sign)) := by
    exact Iff.mp (normalization_3131 c0_node c0_sign c2_node c2_sign) (replay_2185 c0_node c0_sign c2_node c2_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3132 c0_node c0_sign c2_node c2_sign) hn

theorem normalized_788 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3133 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ↔ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_3134 (c0_depth c2_depth : Int) : ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_3135 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := (and_congr (normalization_3133 c0_depth c2_depth) (normalization_3134 c0_depth c2_depth))

abbrev shared_expr_Repair035_30 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))
theorem normalization_3136 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) ↔ (shared_expr_Repair035_30 c0_depth c2_depth) := (iff_congr (normalization_3026 c0_depth c2_depth) (normalization_3135 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2187 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) := by
  classical
  have ht := (normalized_788 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_3136 c0_depth c2_depth) hn

abbrev shared_expr_Repair035_31 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))))
abbrev formula_830 (c0_depth c2_depth : Int) : Prop := (shared_expr_Repair035_31 c0_depth c2_depth)

theorem normalized_789 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3137 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) := (not_congr (normalization_3133 c0_depth c2_depth))

theorem normalization_3138 (c0_depth c2_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_3134 c0_depth c2_depth))

theorem normalization_3139 (c0_depth c2_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int))))) := (or_congr (normalization_3137 c0_depth c2_depth) (normalization_3138 c0_depth c2_depth))

theorem normalization_3140 (c0_depth c2_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))) := (not_congr (normalization_3139 c0_depth c2_depth))

abbrev shared_expr_Repair035_32 (c0_depth c2_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))))))
theorem normalization_3141 (c0_depth c2_depth : Int) : (formula_830 c0_depth c2_depth) ↔ (shared_expr_Repair035_32 c0_depth c2_depth) := (iff_congr (normalization_3135 c0_depth c2_depth) (normalization_3140 c0_depth c2_depth))

-- Checked replay of rewrite.
theorem replay_2188 (c0_depth c2_depth : Int) : (formula_830 c0_depth c2_depth) := by
  classical
  have ht := (normalized_789 ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3141 c0_depth c2_depth) hn

theorem normalized_790 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3142 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) ↔ (shared_expr_Repair035_32 c0_depth c2_depth) := (iff_congr (normalization_3026 c0_depth c2_depth) (normalization_3140 c0_depth c2_depth))

-- Checked replay of trans.
theorem replay_2189 (c0_depth c2_depth : Int) : (((c0_depth + ((-1 : Int) * c2_depth)) = (-1 : Int)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)))))) := by
  classical
  have ht := (normalized_790 (((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair035_32 c0_depth c2_depth))
  have n0 : (shared_expr_Repair035_30 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3136 c0_depth c2_depth) (replay_2187 c0_depth c2_depth)
  have n1 : (shared_expr_Repair035_32 c0_depth c2_depth) := by
    exact Iff.mp (normalization_3141 c0_depth c2_depth) (replay_2188 c0_depth c2_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3142 c0_depth c2_depth) hn

theorem normalized_791 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3143 (c0_node c2_node : Int) : ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_3144 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (and_congr (normalization_3143 c0_node c2_node) (normalization_3028 c0_node c2_node))

abbrev shared_expr_Repair035_33 (c0_node c2_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3145 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ (shared_expr_Repair035_33 c0_node c2_node) := (iff_congr (normalization_3027 c0_node c2_node) (normalization_3144 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2190 (c0_node c2_node : Int) : (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_791 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
  have hn := ht
  exact Iff.mpr (normalization_3145 c0_node c2_node) hn

abbrev shared_expr_Repair035_34 (c0_node c2_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ∧ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_831 (c0_node c2_node : Int) : Prop := (shared_expr_Repair035_34 c0_node c2_node)

theorem normalized_792 (p0 p1 : Prop) : (((¬ p0) ∧ p1) ↔ (¬ ((¬ (¬ p0)) ∨ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3146 (c0_node c2_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_3143 c0_node c2_node))

theorem normalization_3147 (c0_node c2_node : Int) : ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ↔ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) := (or_congr (normalization_3146 c0_node c2_node) (normalization_3029 c0_node c2_node))

theorem normalization_3148 (c0_node c2_node : Int) : (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) := (not_congr (normalization_3147 c0_node c2_node))

abbrev shared_expr_Repair035_35 (c0_node c2_node : Int) : Prop := (((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ↔ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))))
theorem normalization_3149 (c0_node c2_node : Int) : (formula_831 c0_node c2_node) ↔ (shared_expr_Repair035_35 c0_node c2_node) := (iff_congr (normalization_3144 c0_node c2_node) (normalization_3148 c0_node c2_node))

-- Checked replay of rewrite.
theorem replay_2191 (c0_node c2_node : Int) : (formula_831 c0_node c2_node) := by
  classical
  have ht := (normalized_792 (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)) (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_3149 c0_node c2_node) hn

abbrev shared_expr_Repair035_36 (c0_node c2_node : Int) : Prop := (((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))))
abbrev formula_832 (c0_node c2_node : Int) : Prop := (shared_expr_Repair035_36 c0_node c2_node)

theorem normalized_793 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_3150 (c0_node c2_node : Int) : (formula_832 c0_node c2_node) ↔ (shared_expr_Repair035_35 c0_node c2_node) := (iff_congr (normalization_3027 c0_node c2_node) (normalization_3148 c0_node c2_node))

-- Checked replay of trans.
theorem replay_2192 (c0_node c2_node : Int) : (formula_832 c0_node c2_node) := by
  classical
  have ht := (normalized_793 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) (shared_expr_Repair035_35 c0_node c2_node))
  have n0 : (shared_expr_Repair035_33 c0_node c2_node) := by
    exact Iff.mp (normalization_3145 c0_node c2_node) (replay_2190 c0_node c2_node)
  have n1 : (shared_expr_Repair035_35 c0_node c2_node) := by
    exact Iff.mp (normalization_3149 c0_node c2_node) (replay_2191 c0_node c2_node)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3150 c0_node c2_node) hn

abbrev shared_expr_Repair035_37 (c0_node c0_sign c2_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev shared_expr_Repair035_38 (c0_node c2_node : Int) : Prop := ((¬ (¬ ((¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))))) ∧ (¬ ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_833 (c0_node c0_sign c2_node : Int) : Prop := ((shared_expr_Repair035_37 c0_node c0_sign c2_node) ∨ (shared_expr_Repair035_38 c0_node c2_node))

theorem normalized_794 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p4))) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p4))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair035_39 (c0_node c0_sign c2_node : Int) : Prop := ((¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∧ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair035_40 (c0_node c2_node : Int) : Prop := ((¬ (¬ ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
theorem normalization_3151 (c0_node c0_sign c2_node : Int) : (formula_833 c0_node c0_sign c2_node) ↔ ((shared_expr_Repair035_39 c0_node c0_sign c2_node) ∨ (shared_expr_Repair035_40 c0_node c2_node)) := (or_congr (and_congr (normalization_3148 c0_node c2_node) (normalization_461 c0_sign)) (and_congr (not_congr (normalization_3148 c0_node c2_node)) (normalization_3029 c0_node c2_node)))

abbrev shared_expr_Repair035_41 (c0_node c2_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair035_42 (c0_node c0_sign c2_node : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair035_41 c0_node c2_node))
theorem normalization_3152 (c0_node c0_sign c2_node : Int) : ((formula_815 c0_node c0_sign c2_node) ↔ (formula_833 c0_node c0_sign c2_node)) ↔ ((shared_expr_Repair035_42 c0_node c0_sign c2_node) ↔ ((shared_expr_Repair035_39 c0_node c0_sign c2_node) ∨ (shared_expr_Repair035_40 c0_node c2_node))) := (iff_congr (normalization_3030 c0_node c0_sign c2_node) (normalization_3151 c0_node c0_sign c2_node))

-- Checked replay of monotonicity.
theorem replay_2193 (c0_node c0_sign c2_node : Int) : ((formula_815 c0_node c0_sign c2_node) ↔ (formula_833 c0_node c0_sign c2_node)) := by
  classical
  have ht := (normalized_794 ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ((¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int)))) ∨ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))) (((c2_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
  have n0 : (shared_expr_Repair035_35 c0_node c2_node) := by
    exact Iff.mp (normalization_3150 c0_node c2_node) (replay_2192 c0_node c2_node)
  have n1 : ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_sign) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_3117 c0_sign) (replay_2177 c0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_3152 c0_node c0_sign c2_node) hn

end H4Formal.Generated.Repair
