import H4Formal.BooleanReplaySupport
import H4Formal.ArithmeticReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair012

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem normalized_328 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1994 (r0_mode : Int) : (¬ (r0_mode ≤ (5 : Int))) ↔ (¬ ((r0_mode) ≤ (5 : Int))) := (not_congr (normalization_1990 r0_mode))

theorem normalization_1995 (r0_mode : Int) : (¬ (r0_mode ≥ (5 : Int))) ↔ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) := (not_congr (normalization_1991 r0_mode))

theorem normalization_1996 (r0_mode : Int) : ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int)))) ↔ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))) := (or_congr (normalization_1994 r0_mode) (normalization_1995 r0_mode))

theorem normalization_1997 (r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))))) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))))) := (not_congr (normalization_1996 r0_mode))

theorem normalization_1998 (r0_mode : Int) : (((r0_mode ≤ (5 : Int)) ∧ (r0_mode ≥ (5 : Int))) ↔ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int)))))) ↔ ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))) := (iff_congr (normalization_1992 r0_mode) (normalization_1997 r0_mode))

-- Checked replay of rewrite.
theorem replay_441 (r0_mode : Int) : (((r0_mode ≤ (5 : Int)) ∧ (r0_mode ≥ (5 : Int))) ↔ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int)))))) := by
  classical
  have ht := (normalized_328 ((r0_mode) ≤ (5 : Int)) ((r0_mode) ≤ (4 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_1998 r0_mode) hn

theorem normalized_329 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_1999 (r0_mode : Int) : ((r0_mode = (5 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int)))))) ↔ ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))) := (iff_congr (normalization_1478 r0_mode) (normalization_1997 r0_mode))

-- Checked replay of trans.
theorem replay_442 (r0_mode : Int) : ((r0_mode = (5 : Int)) ↔ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int)))))) := by
  classical
  have ht := (normalized_329 (((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))))
  have n0 : ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ↔ (((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int))))) := by
    exact Iff.mp (normalization_1993 r0_mode) (replay_440 r0_mode)
  have n1 : ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))) := by
    exact Iff.mp (normalization_1998 r0_mode) (replay_441 r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_1999 r0_mode) hn

abbrev shared_expr_Repair013_0 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))))) ∧ (¬ ((¬ ((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∧ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))) ∧ ((c1_node % (2 : Int)) ≥ (1 : Int)))
abbrev formula_483 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := (shared_expr_Repair013_0 c1_depth c1_kind c1_node c1_sign r0_level)

theorem normalized_330 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5) ∧ (p6 ↔ p7)) → ((p0 ∧ p2 ∧ p4 ∧ p6) ↔ ((¬ p1) ∧ (¬ p3) ∧ p5 ∧ p7))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_1 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))) ∧ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
theorem normalization_2000 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : (formula_483 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (shared_expr_Repair013_1 c1_depth c1_kind c1_node c1_sign r0_level) := (and_congr (normalization_1784 c1_kind) (and_congr (normalization_1890 c1_depth r0_level) (and_congr (normalization_1846 c1_sign) (normalization_1934 c1_node))))

abbrev shared_expr_Repair013_2 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
theorem normalization_2001 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ (c1_depth = r0_level) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (1 : Int))) ↔ (formula_483 c1_depth c1_kind c1_node c1_sign r0_level)) ↔ ((shared_expr_Repair013_2 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (shared_expr_Repair013_1 c1_depth c1_kind c1_node c1_sign r0_level)) := (iff_congr (normalization_1567 c1_depth c1_kind c1_node c1_sign r0_level) (normalization_2000 c1_depth c1_kind c1_node c1_sign r0_level))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair013_3 (c1_depth r0_level : Int) : Prop := ((((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))))))
abbrev shared_expr_Repair013_4 (c1_sign : Int) : Prop := (((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ↔ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))))
abbrev shared_expr_Repair013_5 (c1_node : Int) : Prop := (((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ↔ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
theorem replay_443 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ (c1_depth = r0_level) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (1 : Int))) ↔ (formula_483 c1_depth c1_kind c1_node c1_sign r0_level)) := by
  classical
  have ht := (normalized_330 (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))) (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))))) ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))) ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have n0 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1786 c1_kind) (replay_358 c1_kind)
  have n1 : (shared_expr_Repair013_3 c1_depth r0_level) := by
    exact Iff.mp (normalization_1893 c1_depth r0_level) (replay_394 c1_depth r0_level)
  have n2 : (shared_expr_Repair013_4 c1_sign) := by
    exact Iff.mp (normalization_1847 c1_sign) (replay_375 c1_sign)
  have n3 : (shared_expr_Repair013_5 c1_node) := by
    exact Iff.mp (normalization_1942 c1_node) (replay_418 c1_node)
  have hn := ht ⟨n0, n1, n2, n3⟩
  exact Iff.mpr (normalization_2001 c1_depth c1_kind c1_node c1_sign r0_level) hn

theorem normalized_331 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ (¬ ((¬ p2) ∨ (¬ (¬ p3)))) ∧ p4 ∧ p5) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p4) ∨ (¬ p2) ∨ (¬ (¬ p3)) ∨ (¬ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_6 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
theorem normalization_2002 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : (formula_356 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level) := (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_1850 c1_sign) (or_congr (normalization_1887 c1_depth r0_level) (or_congr (normalization_1888 c1_depth r0_level) (normalization_1945 c1_node))))))

theorem normalization_2003 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : (¬ (formula_356 c1_depth c1_kind c1_node c1_sign r0_level)) ↔ (¬ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level)) := (not_congr (normalization_2002 c1_depth c1_kind c1_node c1_sign r0_level))

theorem normalization_2004 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : ((formula_483 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (¬ (formula_356 c1_depth c1_kind c1_node c1_sign r0_level))) ↔ ((shared_expr_Repair013_1 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (¬ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level))) := (iff_congr (normalization_2000 c1_depth c1_kind c1_node c1_sign r0_level) (normalization_2003 c1_depth c1_kind c1_node c1_sign r0_level))

-- Checked replay of rewrite.
theorem replay_444 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : ((formula_483 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (¬ (formula_356 c1_depth c1_kind c1_node c1_sign r0_level))) := by
  classical
  have ht := (normalized_331 ((c1_kind) ≤ (1 : Int)) ((c1_kind) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int))))))) ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2004 c1_depth c1_kind c1_node c1_sign r0_level) hn

theorem normalized_332 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2005 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ (c1_depth = r0_level) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_356 c1_depth c1_kind c1_node c1_sign r0_level))) ↔ ((shared_expr_Repair013_2 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (¬ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level))) := (iff_congr (normalization_1567 c1_depth c1_kind c1_node c1_sign r0_level) (normalization_2003 c1_depth c1_kind c1_node c1_sign r0_level))

-- Checked replay of trans.
theorem replay_445 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : (((c1_kind = (1 : Int)) ∧ (c1_depth = r0_level) ∧ ((c1_sign = (1 : Int)) ∨ (c1_sign = (2 : Int))) ∧ ((c1_node % (2 : Int)) = (1 : Int))) ↔ (¬ (formula_356 c1_depth c1_kind c1_node c1_sign r0_level))) := by
  classical
  have ht := (normalized_332 (shared_expr_Repair013_2 c1_depth c1_kind c1_node c1_sign r0_level) (shared_expr_Repair013_1 c1_depth c1_kind c1_node c1_sign r0_level) (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level))
  have n0 : ((shared_expr_Repair013_2 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (shared_expr_Repair013_1 c1_depth c1_kind c1_node c1_sign r0_level)) := by
    exact Iff.mp (normalization_2001 c1_depth c1_kind c1_node c1_sign r0_level) (replay_443 c1_depth c1_kind c1_node c1_sign r0_level)
  have n1 : ((shared_expr_Repair013_1 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (¬ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level))) := by
    exact Iff.mp (normalization_2004 c1_depth c1_kind c1_node c1_sign r0_level) (replay_444 c1_depth c1_kind c1_node c1_sign r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2005 c1_depth c1_kind c1_node c1_sign r0_level) hn

abbrev shared_expr_Repair013_7 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∧ (¬ (formula_356 c1_depth c1_kind c1_node c1_sign r0_level))) ∨ ((¬ (¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))))) ∧ (¬ (formula_348 c1_depth c1_kind c1_sign r0_level))))
abbrev formula_484 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := (shared_expr_Repair013_7 c1_depth c1_kind c1_node c1_sign r0_group r0_level)

theorem normalized_333 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5))) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ (¬ p5))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_8 (c1_depth c1_kind c1_sign r0_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))
abbrev shared_expr_Repair013_9 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := (((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level))) ∨ ((¬ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) ∧ (¬ (shared_expr_Repair013_8 c1_depth c1_kind c1_sign r0_level))))
theorem normalization_2006 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : (formula_484 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_9 c1_depth c1_kind c1_node c1_sign r0_group r0_level) := (or_congr (and_congr (normalization_1764 r0_group) (normalization_2003 c1_depth c1_kind c1_node c1_sign r0_level)) (and_congr (not_congr (normalization_1764 r0_group)) (normalization_1852 c1_depth c1_kind c1_sign r0_level)))

abbrev shared_expr_Repair013_10 (c1_depth c1_kind c1_sign r0_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_11 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_2 c1_depth c1_kind c1_node c1_sign r0_level)) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_10 c1_depth c1_kind c1_sign r0_level)))
theorem normalization_2007 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : ((formula_439 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (formula_484 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ ((shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_9 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := (iff_congr (normalization_1631 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (normalization_2006 c1_depth c1_kind c1_node c1_sign r0_group r0_level))

-- Checked replay of monotonicity.
theorem replay_446 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : ((formula_439 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (formula_484 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_333 (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair013_2 c1_depth c1_kind c1_node c1_sign r0_level) (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level) (shared_expr_Repair013_10 c1_depth c1_kind c1_sign r0_level) (shared_expr_Repair013_8 c1_depth c1_kind c1_sign r0_level))
  have n0 : ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ↔ (¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_1766 r0_group) (replay_352 r0_group)
  have n1 : ((shared_expr_Repair013_2 c1_depth c1_kind c1_node c1_sign r0_level) ↔ (¬ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level))) := by
    exact Iff.mp (normalization_2005 c1_depth c1_kind c1_node c1_sign r0_level) (replay_445 c1_depth c1_kind c1_node c1_sign r0_level)
  have n2 : ((shared_expr_Repair013_10 c1_depth c1_kind c1_sign r0_level) ↔ (¬ (shared_expr_Repair013_8 c1_depth c1_kind c1_sign r0_level))) := by
    exact Iff.mp (normalization_1854 c1_depth c1_kind c1_sign r0_level) (replay_378 c1_depth c1_kind c1_sign r0_level)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2007 c1_depth c1_kind c1_node c1_sign r0_group r0_level) hn

theorem normalized_334 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ (¬ p2))) ↔ ((p0 ∧ (¬ p2)) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_12 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_8 c1_depth c1_kind c1_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level))))
theorem normalization_2008 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level) := (or_congr (and_congr (normalization_1763 r0_group) (normalization_1852 c1_depth c1_kind c1_sign r0_level)) (and_congr (not_congr (normalization_1763 r0_group)) (normalization_2003 c1_depth c1_kind c1_node c1_sign r0_level)))

theorem normalization_2009 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : ((formula_484 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ ((shared_expr_Repair013_9 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := (iff_congr (normalization_2006 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (normalization_2008 c1_depth c1_kind c1_node c1_sign r0_group r0_level))

-- Checked replay of rewrite.
theorem replay_447 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : ((formula_484 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_334 ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) (shared_expr_Repair013_6 c1_depth c1_kind c1_node c1_sign r0_level) (shared_expr_Repair013_8 c1_depth c1_kind c1_sign r0_level))
  have hn := ht
  exact Iff.mpr (normalization_2009 c1_depth c1_kind c1_node c1_sign r0_group r0_level) hn

theorem normalized_335 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2010 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : ((formula_439 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ ((shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := (iff_congr (normalization_1631 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (normalization_2008 c1_depth c1_kind c1_node c1_sign r0_group r0_level))

-- Checked replay of trans.
theorem replay_448 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : ((formula_439 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := by
  classical
  have ht := (normalized_335 (shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (shared_expr_Repair013_9 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level))
  have n0 : ((shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_9 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_2007 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (replay_446 c1_depth c1_kind c1_node c1_sign r0_group r0_level)
  have n1 : ((shared_expr_Repair013_9 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_2009 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (replay_447 c1_depth c1_kind c1_node c1_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2010 c1_depth c1_kind c1_node c1_sign r0_group r0_level) hn

abbrev shared_expr_Repair013_13 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (5 : Int)) ∧ (formula_439 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ ((¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))))) ∧ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))
abbrev formula_485 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair013_13 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)

theorem normalized_336 (p0 p1 p2 p3 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3)) → ((p0 ∧ p2) ↔ ((¬ p1) ∧ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2011 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : ((¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))))) ∧ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))))) ∧ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := (and_congr (normalization_1997 r0_mode) (normalization_2008 c1_depth c1_kind c1_node c1_sign r0_group r0_level))

abbrev shared_expr_Repair013_14 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ ((¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))))) ∧ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))
theorem normalization_2012 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_485 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_14 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := (iff_congr (normalization_1632 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (normalization_2011 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_449 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_485 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_336 (((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))) (shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level))
  have n0 : ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int))))))) := by
    exact Iff.mp (normalization_1999 r0_mode) (replay_442 r0_mode)
  have n1 : ((shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level) ↔ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := by
    exact Iff.mp (normalization_2010 c1_depth c1_kind c1_node c1_sign r0_group r0_level) (replay_448 c1_depth c1_kind c1_node c1_sign r0_group r0_level)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2012 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair013_15 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))))) ∧ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))) ∨ (¬ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
abbrev formula_486 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair013_15 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)

theorem normalized_337 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∧ p2) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1)) ∨ (¬ p2)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2013 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : (¬ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := (not_congr (normalization_2008 c1_depth c1_kind c1_node c1_sign r0_group r0_level))

theorem normalization_2014 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))) ∨ (¬ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level))) ↔ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level))) := (or_congr (normalization_1994 r0_mode) (or_congr (normalization_1995 r0_mode) (normalization_2013 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))

theorem normalization_2015 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))) ∨ (¬ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))) := (not_congr (normalization_2014 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))

abbrev shared_expr_Repair013_16 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))))) ∧ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
theorem normalization_2016 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_486 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_16 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := (iff_congr (normalization_2011 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (normalization_2015 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_450 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_486 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_337 ((r0_mode) ≤ (5 : Int)) ((r0_mode) ≤ (4 : Int)) (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level))
  have hn := ht
  exact Iff.mpr (normalization_2016 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair013_17 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((r0_mode = (5 : Int)) ∧ (formula_439 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ ((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))) ∨ (¬ (formula_357 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
abbrev formula_487 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair013_17 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)

theorem normalized_338 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ (¬ p2))) → (p0 ↔ (¬ p2))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_18 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
theorem normalization_2017 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_487 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_18 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := (iff_congr (normalization_1632 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (normalization_2015 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_451 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_487 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_338 ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ((¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))))) ∧ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level))))
  have n0 : (shared_expr_Repair013_14 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_2012 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_449 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair013_16 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_2016 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_450 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2017 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) hn

theorem normalized_339 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ (¬ p5)) ∧ (p6 ↔ (¬ p7)) ∧ (p8 ↔ (¬ p9)) ∧ (p10 ↔ (¬ p11))) → ((p0 ∨ p2 ∨ p4 ∨ p6 ∨ p8 ∨ p10) ↔ ((¬ p1) ∨ (¬ p3) ∨ (¬ p5) ∨ (¬ p7) ∨ (¬ p9) ∨ (¬ p11)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_19 (c1_depth c1_kind c1_sign r0_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))))
abbrev shared_expr_Repair013_20 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_19 c1_depth c1_kind c1_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Repair013_21 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_8 c1_depth c1_kind c1_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))))
abbrev shared_expr_Repair013_22 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair013_23 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_22 c1_depth c1_kind c1_node c1_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_19 c1_depth c1_kind c1_sign r0_level))))
abbrev shared_expr_Repair013_24 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair013_25 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_24 c1_depth c1_kind c1_node c1_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_19 c1_depth c1_kind c1_sign r0_level))))
abbrev shared_expr_Repair013_26 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))))))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair013_27 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := ((((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_8 c1_depth c1_kind c1_sign r0_level))) ∨ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_26 c1_depth c1_kind c1_node c1_sign r0_level))))
abbrev shared_expr_Repair013_28 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair013_20 c1_depth c1_kind c1_sign r0_group r0_level)))) ∨ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair013_21 c1_depth c1_kind c1_sign r0_group r0_level)))) ∨ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair013_23 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))) ∨ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair013_25 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))) ∨ (¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair013_27 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))) ∨ (¬ ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
theorem normalization_2018 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := (or_congr (normalization_1827 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (or_congr (normalization_1864 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (or_congr (normalization_1920 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (or_congr (normalization_1959 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (or_congr (normalization_1987 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (normalization_2015 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))))))

abbrev shared_expr_Repair013_29 (c1_depth c1_kind c1_sign r0_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_30 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_29 c1_depth c1_kind c1_sign r0_level)))
abbrev shared_expr_Repair013_31 (c1_depth c1_kind c1_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_10 c1_depth c1_kind c1_sign r0_level)))
abbrev shared_expr_Repair013_32 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair013_33 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_29 c1_depth c1_kind c1_sign r0_level)) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_32 c1_depth c1_kind c1_node c1_sign r0_level)))
abbrev shared_expr_Repair013_34 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair013_35 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_29 c1_depth c1_kind c1_sign r0_level)) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_34 c1_depth c1_kind c1_node c1_sign r0_level)))
abbrev shared_expr_Repair013_36 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : Prop := ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * r0_level)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∧ ((((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (c1_node / (2 : Int))) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair013_37 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : Prop := (((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_36 c1_depth c1_kind c1_node c1_sign r0_level)) ∨ ((¬ (((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_10 c1_depth c1_kind c1_sign r0_level)))
abbrev shared_expr_Repair013_38 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair013_30 c1_depth c1_kind c1_sign r0_group r0_level)) ∨ ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_31 c1_depth c1_kind c1_sign r0_group r0_level)) ∨ ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair013_33 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ∨ ((((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair013_35 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ∨ ((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair013_37 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ∨ ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))
theorem normalization_2019 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : ((formula_440 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) ↔ ((shared_expr_Repair013_38 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := (iff_congr (normalization_1633 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (normalization_2018 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
abbrev shared_expr_Repair013_39 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair013_30 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair013_20 c1_depth c1_kind c1_sign r0_group r0_level)))))
abbrev shared_expr_Repair013_40 (c1_depth c1_kind c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_31 c1_depth c1_kind c1_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair013_21 c1_depth c1_kind c1_sign r0_group r0_level)))))
abbrev shared_expr_Repair013_41 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair013_33 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair013_23 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
abbrev shared_expr_Repair013_42 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair013_35 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair013_25 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
abbrev shared_expr_Repair013_43 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair013_37 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ↔ (¬ ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair013_27 c1_depth c1_kind c1_node c1_sign r0_group r0_level)))))
theorem replay_452 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : ((formula_440 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := by
  classical
  have ht := (normalized_339 ((((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair013_30 c1_depth c1_kind c1_sign r0_group r0_level)) ((¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair013_20 c1_depth c1_kind c1_sign r0_group r0_level))) ((((r0_mode) ≤ (1 : Int)) ∧ (¬ ((r0_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_31 c1_depth c1_kind c1_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair013_21 c1_depth c1_kind c1_sign r0_group r0_level))) ((((r0_mode) ≤ (2 : Int)) ∧ (¬ ((r0_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair013_33 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair013_23 c1_depth c1_kind c1_node c1_sign r0_group r0_level))) ((((r0_mode) ≤ (3 : Int)) ∧ (¬ ((r0_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair013_35 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair013_25 c1_depth c1_kind c1_node c1_sign r0_group r0_level))) ((((r0_mode) ≤ (4 : Int)) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair013_37 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair013_27 c1_depth c1_kind c1_node c1_sign r0_group r0_level))) ((((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair013_11 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_12 c1_depth c1_kind c1_node c1_sign r0_group r0_level))))
  have n0 : (shared_expr_Repair013_39 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_1829 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (replay_371 c1_depth c1_kind c1_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair013_40 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_1866 c1_depth c1_kind c1_sign r0_group r0_level r0_mode) (replay_384 c1_depth c1_kind c1_sign r0_group r0_level r0_mode)
  have n2 : (shared_expr_Repair013_41 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_1922 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_409 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have n3 : (shared_expr_Repair013_42 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_1961 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_427 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have n4 : (shared_expr_Repair013_43 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_1989 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_439 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have n5 : (shared_expr_Repair013_18 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_2017 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_451 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1, n2, n3, n4, n5⟩
  exact Iff.mpr (normalization_2019 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) hn

theorem normalized_340 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2020 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : ((formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) ↔ ((shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := (iff_congr (normalization_2018 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (normalization_2018 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_453 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : ((formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := by
  classical
  have ht := (normalized_340 (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))
  have hn := ht
  exact Iff.mpr (normalization_2020 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) hn

theorem normalized_341 (p0 p1 : Prop) : ((p0 ∧ (p1 ↔ p1)) → p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of trans.
theorem replay_454 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : ((formula_440 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := by
  classical
  have ht := (normalized_341 ((shared_expr_Repair013_38 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))
  have n0 : ((shared_expr_Repair013_38 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := by
    exact Iff.mp (normalization_2019 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_452 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have n1 : ((shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := by
    exact Iff.mp (normalization_2020 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_453 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2019 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair013_44 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∧ (¬ (formula_345 c1_group c1_level c1_mode r0_group r0_level r0_mode))) ∨ ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ∧ (formula_358 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)))
abbrev formula_488 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair013_44 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)

abbrev shared_expr_Repair013_45 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((formula_441 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_488 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))
abbrev formula_489 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair013_45 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)

theorem normalized_342 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ (¬ p3)) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ (¬ p3)) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_46 (c1_group c1_level c1_mode r0_group r0_level r0_mode : Int) : Prop := ((¬ (¬ ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int)))) ∨ (¬ ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∨ (¬ ((¬ (¬ ((c1_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int)))) ∨ (¬ ((c1_group + ((-1 : Int) * r0_group)) ≤ (0 : Int))))))
abbrev shared_expr_Repair013_47 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Repair013_46 c1_group c1_level c1_mode r0_group r0_level r0_mode))) ∨ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)))
theorem normalization_2021 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_488 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_47 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := (or_congr (and_congr (normalization_1683 c1_kind) (normalization_1744 c1_group c1_level c1_mode r0_group r0_level r0_mode)) (and_congr (not_congr (normalization_1683 c1_kind)) (normalization_2018 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)))

abbrev shared_expr_Repair013_48 (c1_group c1_level c1_mode r0_group r0_level r0_mode : Int) : Prop := (((¬ ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (-1 : Int))) ∧ ((c1_mode + ((-1 : Int) * r0_mode)) ≤ (0 : Int))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_level)) ≤ (0 : Int))) ∧ (¬ ((¬ ((c1_group + ((-1 : Int) * r0_group)) ≤ (-1 : Int))) ∧ ((c1_group + ((-1 : Int) * r0_group)) ≤ (0 : Int)))))
abbrev shared_expr_Repair013_49 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair013_48 c1_group c1_level c1_mode r0_group r0_level r0_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair013_38 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)))
abbrev shared_expr_Repair013_50 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((shared_expr_Repair013_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_47 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))
theorem normalization_2022 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_489 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_50 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := (iff_congr (normalization_1634 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (normalization_2021 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of monotonicity.
theorem replay_455 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_489 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_342 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair013_48 c1_group c1_level c1_mode r0_group r0_level r0_mode) (shared_expr_Repair013_46 c1_group c1_level c1_mode r0_group r0_level r0_mode) (shared_expr_Repair013_38 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1685 c1_kind) (replay_319 c1_kind)
  have n1 : ((shared_expr_Repair013_48 c1_group c1_level c1_mode r0_group r0_level r0_mode) ↔ (¬ (shared_expr_Repair013_46 c1_group c1_level c1_mode r0_group r0_level r0_mode))) := by
    exact Iff.mp (normalization_1746 c1_group c1_level c1_mode r0_group r0_level r0_mode) (replay_346 c1_group c1_level c1_mode r0_group r0_level r0_mode)
  have n2 : ((shared_expr_Repair013_38 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) := by
    exact Iff.mp (normalization_2019 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode) (replay_454 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2022 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair013_51 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((formula_488 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))
abbrev formula_490 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair013_51 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)

theorem normalized_343 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ (¬ p1)) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_52 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) ∨ ((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (¬ (shared_expr_Repair013_46 c1_group c1_level c1_mode r0_group r0_level r0_mode))))
theorem normalization_2023 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := (or_congr (and_congr (normalization_1682 c1_kind) (normalization_2018 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode)) (and_congr (not_congr (normalization_1682 c1_kind)) (normalization_1744 c1_group c1_level c1_mode r0_group r0_level r0_mode)))

abbrev shared_expr_Repair013_53 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((shared_expr_Repair013_47 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))
theorem normalization_2024 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_490 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_53 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := (iff_congr (normalization_2021 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (normalization_2023 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of rewrite.
theorem replay_456 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_490 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_343 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair013_46 c1_group c1_level c1_mode r0_group r0_level r0_mode) (shared_expr_Repair013_28 c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode))
  have hn := ht
  exact Iff.mpr (normalization_2024 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) hn

abbrev shared_expr_Repair013_54 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((formula_441 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))
abbrev formula_491 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := (shared_expr_Repair013_54 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)

theorem normalized_344 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_55 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : Prop := ((shared_expr_Repair013_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))
theorem normalization_2025 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_491 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) ↔ (shared_expr_Repair013_55 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := (iff_congr (normalization_1634 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (normalization_2023 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))

-- Checked replay of trans.
theorem replay_457 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) : (formula_491 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := by
  classical
  have ht := (normalized_344 (shared_expr_Repair013_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (shared_expr_Repair013_47 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode))
  have n0 : (shared_expr_Repair013_50 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_2022 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (replay_455 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)
  have n1 : (shared_expr_Repair013_53 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_2024 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (replay_456 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2025 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) hn

-- Checked replay of rewrite.
theorem replay_458 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : ((formula_444 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) ↔ (formula_384 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) := by
  classical
  first
  | (simp only [formula_444, formula_442, formula_443, formula_418, formula_419, formula_420, formula_421, formula_384, formula_372, formula_370, formula_371, formula_375, formula_373, formula_374, formula_377, formula_376, formula_379, formula_378, formula_381, formula_380, formula_383, formula_382, H4Formal.parity_eq_zero, H4Formal.parity_eq_one]
     simp only [H4Formal.int_eq_bounds, H4Formal.int_difference_le_zero, H4Formal.int_difference_ge_zero, Classical.not_not, not_or, Classical.not_and_iff_not_or_not, GE.ge]
     first | done | (apply Iff.of_eq; ac_rfl))
  | omega
  | grind (splits := 40)

theorem normalized_345 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : (((((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3))) ∧ (¬ ((p0 ∧ (¬ p1)) ∧ (p3 ∧ (¬ p4)) ∧ (p5 ∧ (¬ p6))))) ∨ ((¬ ((p0 ∧ (¬ p1)) ∨ (p2 ∧ (¬ p3)))) ∧ ((((¬ p7) ∧ p8) ∧ (((p9 ∧ (¬ p10)) ∧ (p11 ∧ (¬ p12)) ∧ (¬ p13)) ∨ ((p14 ∧ (¬ p15)) ∧ (p16 ∧ (¬ p17)) ∧ ((¬ p18) ∧ p19) ∧ (¬ p13)) ∨ ((p15 ∧ (¬ p9)) ∧ (p17 ∧ (¬ p11)) ∧ (¬ p19) ∧ (¬ p20)))) ∨ (((¬ p21) ∧ p7) ∧ ((((p9 ∧ (¬ p10)) ∨ (p14 ∧ (¬ p15))) ∧ (p11 ∧ (¬ p12)) ∧ p22) ∨ (((p15 ∧ (¬ p9)) ∨ (p14 ∧ (¬ p15))) ∧ (p17 ∧ (¬ p11)) ∧ (¬ (¬ p23)))))))) ↔ ((((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3))))) ∧ ((¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p3) ∨ (¬ (¬ p4)) ∨ (¬ p5) ∨ (¬ (¬ p6)))) ∨ ((¬ ((¬ ((¬ p0) ∨ (¬ (¬ p1)))) ∨ (¬ ((¬ p2) ∨ (¬ (¬ p3)))))) ∧ ((¬ ((¬ (¬ p7)) ∨ (¬ p8) ∨ (¬ ((¬ ((¬ p9) ∨ (¬ (¬ p10)) ∨ (¬ p11) ∨ (¬ (¬ p12)) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p19) ∨ (¬ (¬ p18)) ∨ (¬ p14) ∨ (¬ (¬ p15)) ∨ (¬ p16) ∨ (¬ (¬ p17)) ∨ (¬ (¬ p13)))) ∨ (¬ (p19 ∨ p20 ∨ (¬ (¬ p9)) ∨ (¬ p15) ∨ (¬ p17) ∨ (¬ (¬ p11)))))))) ∨ (¬ ((¬ (¬ p21)) ∨ (¬ p7) ∨ (¬ ((¬ ((¬ p11) ∨ (¬ (¬ p12)) ∨ (¬ ((¬ ((¬ p9) ∨ (¬ (¬ p10)))) ∨ (¬ ((¬ p14) ∨ (¬ (¬ p15)))))) ∨ (¬ p22))) ∨ (¬ ((¬ p23) ∨ (¬ p17) ∨ (¬ (¬ p11)) ∨ (¬ ((¬ ((¬ p15) ∨ (¬ (¬ p9)))) ∨ (¬ ((¬ p14) ∨ (¬ (¬ p15)))))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2026 (r0_kind : Int) : (r0_kind ≤ (2 : Int)) ↔ ((r0_kind) ≤ (2 : Int)) := by
  omega

theorem normalization_2027 (r0_kind : Int) : (¬ (r0_kind ≤ (2 : Int))) ↔ (¬ ((r0_kind) ≤ (2 : Int))) := (not_congr (normalization_2026 r0_kind))

theorem normalization_2028 (r0_kind : Int) : (r0_kind ≥ (2 : Int)) ↔ (¬ ((r0_kind) ≤ (1 : Int))) := by
  omega

theorem normalization_2029 (r0_kind : Int) : (¬ (r0_kind ≥ (2 : Int))) ↔ (¬ (¬ ((r0_kind) ≤ (1 : Int)))) := (not_congr (normalization_2028 r0_kind))

theorem normalization_2030 (r0_kind : Int) : ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))) ↔ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))) := (or_congr (normalization_2027 r0_kind) (normalization_2029 r0_kind))

theorem normalization_2031 (r0_kind : Int) : (¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) ↔ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) := (not_congr (normalization_2030 r0_kind))

theorem normalization_2032 (c1_kind r0_kind : Int) : ((¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := (or_congr (normalization_2031 r0_kind) (normalization_1774 c1_kind))

theorem normalization_2033 (c1_depth h : Int) : ((h + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int)) := by
  omega

theorem normalization_2034 (c1_depth h : Int) : (¬ ((h + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int))) := (not_congr (normalization_2033 c1_depth h))

theorem normalization_2035 (c1_depth h : Int) : ((h + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2036 (c1_depth h : Int) : (¬ ((h + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))) := (not_congr (normalization_2035 c1_depth h))

abbrev shared_expr_Repair013_56 (c1_depth c1_kind h r0_kind : Int) : Prop := ((¬ (¬ ((r0_kind) ≤ (1 : Int)))) ∨ (¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
theorem normalization_2037 (c1_depth c1_kind h r0_kind : Int) : (formula_361 c1_depth c1_kind h r0_kind) ↔ (shared_expr_Repair013_56 c1_depth c1_kind h r0_kind) := (or_congr (normalization_2029 r0_kind) (or_congr (normalization_2027 r0_kind) (or_congr (normalization_1781 c1_kind) (or_congr (normalization_1782 c1_kind) (or_congr (normalization_2034 c1_depth h) (normalization_2036 c1_depth h))))))

theorem normalization_2038 (c1_depth r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2039 (c1_depth r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2038 c1_depth r0_depth))

theorem normalization_2040 (c1_depth r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2041 (c1_depth r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) := (not_congr (normalization_2040 c1_depth r0_depth))

theorem normalization_2042 (r0_sign : Int) : (r0_sign ≤ (0 : Int)) ↔ ((r0_sign) ≤ (0 : Int)) := by
  omega

theorem normalization_2043 (r0_sign : Int) : (¬ (r0_sign ≤ (0 : Int))) ↔ (¬ ((r0_sign) ≤ (0 : Int))) := (not_congr (normalization_2042 r0_sign))

theorem normalization_2044 (r0_sign : Int) : (r0_sign ≥ (0 : Int)) ↔ (¬ ((r0_sign) ≤ (-1 : Int))) := by
  omega

theorem normalization_2045 (r0_sign : Int) : (¬ (r0_sign ≥ (0 : Int))) ↔ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))) := (not_congr (normalization_2044 r0_sign))

theorem normalization_2046 (c1_node r0_node : Int) : (¬ ((r0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_1643 c1_node r0_node))

theorem normalization_2047 (c1_node c1_sign r0_node r0_sign : Int) : ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ↔ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int))))) := (or_congr (normalization_2043 r0_sign) (or_congr (normalization_2045 r0_sign) (or_congr (normalization_1798 c1_sign) (or_congr (normalization_1800 c1_sign) (normalization_2046 c1_node r0_node)))))

theorem normalization_2048 (c1_node c1_sign r0_node r0_sign : Int) : (¬ ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ↔ (¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))))) := (not_congr (normalization_2047 c1_node c1_sign r0_node r0_sign))

theorem normalization_2049 (h r0_depth : Int) : ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int)) ↔ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2050 (h r0_depth : Int) : (¬ ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2049 h r0_depth))

theorem normalization_2051 (r0_sign : Int) : (r0_sign ≤ (2 : Int)) ↔ ((r0_sign) ≤ (2 : Int)) := by
  omega

theorem normalization_2052 (r0_sign : Int) : (¬ (r0_sign ≤ (2 : Int))) ↔ (¬ ((r0_sign) ≤ (2 : Int))) := (not_congr (normalization_2051 r0_sign))

theorem normalization_2053 (r0_sign : Int) : (r0_sign ≥ (2 : Int)) ↔ (¬ ((r0_sign) ≤ (1 : Int))) := by
  omega

theorem normalization_2054 (r0_sign : Int) : (¬ (r0_sign ≥ (2 : Int))) ↔ (¬ (¬ ((r0_sign) ≤ (1 : Int)))) := (not_congr (normalization_2053 r0_sign))

abbrev shared_expr_Repair013_57 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))) ∨ (¬ ((c1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))))
theorem normalization_2055 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (formula_362 c1_node c1_sign h r0_depth r0_node r0_sign) ↔ (shared_expr_Repair013_57 c1_node c1_sign h r0_depth r0_node r0_sign) := (or_congr (normalization_1647 h r0_depth) (or_congr (normalization_2050 h r0_depth) (or_congr (normalization_2052 r0_sign) (or_congr (normalization_2054 r0_sign) (or_congr (normalization_1804 c1_sign) (or_congr (normalization_1806 c1_sign) (normalization_2046 c1_node r0_node)))))))

theorem normalization_2056 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (¬ (formula_362 c1_node c1_sign h r0_depth r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_57 c1_node c1_sign h r0_depth r0_node r0_sign)) := (not_congr (normalization_2055 c1_node c1_sign h r0_depth r0_node r0_sign))

theorem normalization_2057 (r0_sign : Int) : (r0_sign ≥ (1 : Int)) ↔ (¬ ((r0_sign) ≤ (0 : Int))) := by
  omega

theorem normalization_2058 (r0_sign : Int) : (¬ (r0_sign ≥ (1 : Int))) ↔ (¬ (¬ ((r0_sign) ≤ (0 : Int)))) := (not_congr (normalization_2057 r0_sign))

theorem normalization_2059 (r0_sign : Int) : (r0_sign ≤ (1 : Int)) ↔ ((r0_sign) ≤ (1 : Int)) := by
  omega

theorem normalization_2060 (r0_sign : Int) : (¬ (r0_sign ≤ (1 : Int))) ↔ (¬ ((r0_sign) ≤ (1 : Int))) := (not_congr (normalization_2059 r0_sign))

abbrev shared_expr_Repair013_58 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := (((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int)) ∨ ((c1_node + ((-1 : Int) * r0_node)) ≤ (0 : Int)) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))))
theorem normalization_2061 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (formula_363 c1_node c1_sign h r0_depth r0_node r0_sign) ↔ (shared_expr_Repair013_58 c1_node c1_sign h r0_depth r0_node r0_sign) := (or_congr (normalization_1646 h r0_depth) (or_congr (normalization_1648 c1_node r0_node) (or_congr (normalization_2058 r0_sign) (or_congr (normalization_2060 r0_sign) (or_congr (normalization_1841 c1_sign) (normalization_1843 c1_sign))))))

theorem normalization_2062 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (¬ (formula_363 c1_node c1_sign h r0_depth r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_58 c1_node c1_sign h r0_depth r0_node r0_sign)) := (not_congr (normalization_2061 c1_node c1_sign h r0_depth r0_node r0_sign))

abbrev shared_expr_Repair013_59 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))))) ∨ (¬ (shared_expr_Repair013_57 c1_node c1_sign h r0_depth r0_node r0_sign)) ∨ (¬ (shared_expr_Repair013_58 c1_node c1_sign h r0_depth r0_node r0_sign)))
theorem normalization_2063 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (formula_364 c1_node c1_sign h r0_depth r0_node r0_sign) ↔ (shared_expr_Repair013_59 c1_node c1_sign h r0_depth r0_node r0_sign) := (or_congr (normalization_2048 c1_node c1_sign r0_node r0_sign) (or_congr (normalization_2056 c1_node c1_sign h r0_depth r0_node r0_sign) (normalization_2062 c1_node c1_sign h r0_depth r0_node r0_sign)))

theorem normalization_2064 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (¬ (formula_364 c1_node c1_sign h r0_depth r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_59 c1_node c1_sign h r0_depth r0_node r0_sign)) := (not_congr (normalization_2063 c1_node c1_sign h r0_depth r0_node r0_sign))

theorem normalization_2065 (c1_depth c1_node c1_sign h r0_depth r0_node r0_sign : Int) : ((¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_364 c1_node c1_sign h r0_depth r0_node r0_sign))) ↔ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair013_59 c1_node c1_sign h r0_depth r0_node r0_sign))) := (or_congr (normalization_2039 c1_depth r0_depth) (or_congr (normalization_2041 c1_depth r0_depth) (normalization_2064 c1_node c1_sign h r0_depth r0_node r0_sign)))

theorem normalization_2066 (c1_depth c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (¬ ((¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_364 c1_node c1_sign h r0_depth r0_node r0_sign)))) ↔ (¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair013_59 c1_node c1_sign h r0_depth r0_node r0_sign)))) := (not_congr (normalization_2065 c1_depth c1_node c1_sign h r0_depth r0_node r0_sign))

theorem normalization_2067 (c1_depth r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-2 : Int))) := by
  omega

theorem normalization_2068 (c1_depth r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ↔ (¬ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-2 : Int)))) := (not_congr (normalization_2067 c1_depth r0_depth))

theorem normalization_2069 (c1_depth r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ↔ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2070 (c1_depth r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ↔ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) := (not_congr (normalization_2069 c1_depth r0_depth))

theorem normalization_2071 (r0_sign : Int) : ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int)))) ↔ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int))))) := (or_congr (normalization_2043 r0_sign) (normalization_2045 r0_sign))

theorem normalization_2072 (r0_sign : Int) : (¬ ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))))) ↔ (¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) := (not_congr (normalization_2071 r0_sign))

theorem normalization_2073 (r0_sign : Int) : ((¬ (r0_sign ≤ (2 : Int))) ∨ (¬ (r0_sign ≥ (2 : Int)))) ↔ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int))))) := (or_congr (normalization_2052 r0_sign) (normalization_2054 r0_sign))

theorem normalization_2074 (r0_sign : Int) : (¬ ((¬ (r0_sign ≤ (2 : Int))) ∨ (¬ (r0_sign ≥ (2 : Int))))) ↔ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))) := (not_congr (normalization_2073 r0_sign))

theorem normalization_2075 (r0_sign : Int) : ((¬ ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r0_sign ≤ (2 : Int))) ∨ (¬ (r0_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int))))))) := (or_congr (normalization_2072 r0_sign) (normalization_2074 r0_sign))

theorem normalization_2076 (r0_sign : Int) : (¬ ((¬ ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r0_sign ≤ (2 : Int))) ∨ (¬ (r0_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_2075 r0_sign))

theorem normalization_2077 (c1_node r0_node : Int) : (¬ ((c1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := (not_congr (normalization_1654 c1_node r0_node))

abbrev shared_expr_Repair013_60 (c1_node c1_sign r0_node r0_sign : Int) : Prop := ((¬ ((c1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))))
theorem normalization_2078 (c1_node c1_sign r0_node r0_sign : Int) : (formula_365 c1_node c1_sign r0_node r0_sign) ↔ (shared_expr_Repair013_60 c1_node c1_sign r0_node r0_sign) := (or_congr (normalization_1798 c1_sign) (or_congr (normalization_1800 c1_sign) (or_congr (normalization_2076 r0_sign) (normalization_2077 c1_node r0_node))))

theorem normalization_2079 (c1_node c1_sign r0_node r0_sign : Int) : (¬ (formula_365 c1_node c1_sign r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_60 c1_node c1_sign r0_node r0_sign)) := (not_congr (normalization_2078 c1_node c1_sign r0_node r0_sign))

theorem normalization_2080 (r0_sign : Int) : ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int)))) ↔ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int))))) := (or_congr (normalization_2060 r0_sign) (normalization_2058 r0_sign))

theorem normalization_2081 (r0_sign : Int) : (¬ ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int))))) ↔ (¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) := (not_congr (normalization_2080 r0_sign))

theorem normalization_2082 (r0_sign : Int) : ((¬ ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r0_sign ≤ (2 : Int))) ∨ (¬ (r0_sign ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int))))))) := (or_congr (normalization_2081 r0_sign) (normalization_2074 r0_sign))

theorem normalization_2083 (r0_sign : Int) : (¬ ((¬ ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r0_sign ≤ (2 : Int))) ∨ (¬ (r0_sign ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) := (not_congr (normalization_2082 r0_sign))

abbrev shared_expr_Repair013_61 (c1_node c1_sign r0_node r0_sign : Int) : Prop := ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∨ (¬ ((c1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_sign) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))))
theorem normalization_2084 (c1_node c1_sign r0_node r0_sign : Int) : (formula_366 c1_node c1_sign r0_node r0_sign) ↔ (shared_expr_Repair013_61 c1_node c1_sign r0_node r0_sign) := (or_congr (normalization_1656 c1_node r0_node) (or_congr (normalization_1841 c1_sign) (or_congr (normalization_1843 c1_sign) (normalization_2083 r0_sign))))

theorem normalization_2085 (c1_node c1_sign r0_node r0_sign : Int) : (¬ (formula_366 c1_node c1_sign r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_61 c1_node c1_sign r0_node r0_sign)) := (not_congr (normalization_2084 c1_node c1_sign r0_node r0_sign))

theorem normalization_2086 (c1_node c1_sign r0_node r0_sign : Int) : ((¬ (formula_365 c1_node c1_sign r0_node r0_sign)) ∨ (¬ (formula_366 c1_node c1_sign r0_node r0_sign))) ↔ ((¬ (shared_expr_Repair013_60 c1_node c1_sign r0_node r0_sign)) ∨ (¬ (shared_expr_Repair013_61 c1_node c1_sign r0_node r0_sign))) := (or_congr (normalization_2079 c1_node c1_sign r0_node r0_sign) (normalization_2085 c1_node c1_sign r0_node r0_sign))

theorem normalization_2087 (c1_node c1_sign r0_node r0_sign : Int) : (¬ ((¬ (formula_365 c1_node c1_sign r0_node r0_sign)) ∨ (¬ (formula_366 c1_node c1_sign r0_node r0_sign)))) ↔ (¬ ((¬ (shared_expr_Repair013_60 c1_node c1_sign r0_node r0_sign)) ∨ (¬ (shared_expr_Repair013_61 c1_node c1_sign r0_node r0_sign)))) := (not_congr (normalization_2086 c1_node c1_sign r0_node r0_sign))

abbrev shared_expr_Repair013_62 (c1_depth c1_node c1_sign r0_depth r0_node r0_sign : Int) : Prop := ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-2 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∨ (¬ ((¬ (shared_expr_Repair013_60 c1_node c1_sign r0_node r0_sign)) ∨ (¬ (shared_expr_Repair013_61 c1_node c1_sign r0_node r0_sign)))))
theorem normalization_2088 (c1_depth c1_node c1_sign r0_depth r0_node r0_sign : Int) : (formula_367 c1_depth c1_node c1_sign r0_depth r0_node r0_sign) ↔ (shared_expr_Repair013_62 c1_depth c1_node c1_sign r0_depth r0_node r0_sign) := (or_congr (normalization_2068 c1_depth r0_depth) (or_congr (normalization_2070 c1_depth r0_depth) (normalization_2087 c1_node c1_sign r0_node r0_sign)))

theorem normalization_2089 (c1_depth c1_node c1_sign r0_depth r0_node r0_sign : Int) : (¬ (formula_367 c1_depth c1_node c1_sign r0_depth r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_62 c1_depth c1_node c1_sign r0_depth r0_node r0_sign)) := (not_congr (normalization_2088 c1_depth c1_node c1_sign r0_depth r0_node r0_sign))

abbrev shared_expr_Repair013_63 (c1_depth c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := ((¬ ((¬ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ (shared_expr_Repair013_59 c1_node c1_sign h r0_depth r0_node r0_sign)))) ∨ (¬ (shared_expr_Repair013_62 c1_depth c1_node c1_sign r0_depth r0_node r0_sign)))
theorem normalization_2090 (c1_depth c1_node c1_sign h r0_depth r0_node r0_sign : Int) : (formula_368 c1_depth c1_node c1_sign h r0_depth r0_node r0_sign) ↔ (shared_expr_Repair013_63 c1_depth c1_node c1_sign h r0_depth r0_node r0_sign) := (or_congr (normalization_2066 c1_depth c1_node c1_sign h r0_depth r0_node r0_sign) (normalization_2089 c1_depth c1_node c1_sign r0_depth r0_node r0_sign))

abbrev shared_expr_Repair013_64 (c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((¬ ((¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) ∧ (shared_expr_Repair013_63 c1_depth c1_node c1_sign h r0_depth r0_node r0_sign))
abbrev shared_expr_Repair013_65 (c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))))) ∨ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ∧ (shared_expr_Repair013_56 c1_depth c1_kind h r0_kind)) ∨ (shared_expr_Repair013_64 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
theorem normalization_2091 (c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_369 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_65 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := (or_congr (and_congr (normalization_2032 c1_kind r0_kind) (normalization_2037 c1_depth c1_kind h r0_kind)) (and_congr (not_congr (normalization_2032 c1_kind r0_kind)) (normalization_2090 c1_depth c1_node c1_sign h r0_depth r0_node r0_sign)))

abbrev shared_expr_Repair013_66 (c1_depth c1_kind h r0_kind : Int) : Prop := ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ∧ (((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ (¬ ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair013_67 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := ((((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int)))) ∧ (((c1_sign) ≤ (2 : Int)) ∧ (¬ ((c1_sign) ≤ (1 : Int)))) ∧ ((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair013_68 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair013_69 (c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := (((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) ∨ (shared_expr_Repair013_67 c1_node c1_sign h r0_depth r0_node r0_sign) ∨ (shared_expr_Repair013_68 c1_node c1_sign h r0_depth r0_node r0_sign))
abbrev shared_expr_Repair013_70 (c1_node c1_sign r0_node r0_sign : Int) : Prop := (((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (0 : Int)) ∧ (¬ ((c1_sign) ≤ (-1 : Int)))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))
abbrev shared_expr_Repair013_71 (c1_node c1_sign r0_node r0_sign : Int) : Prop := (((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) ∧ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair013_72 (c1_depth c1_node c1_sign r0_depth r0_node r0_sign : Int) : Prop := (((¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-2 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((shared_expr_Repair013_70 c1_node c1_sign r0_node r0_sign) ∨ (shared_expr_Repair013_71 c1_node c1_sign r0_node r0_sign)))
abbrev shared_expr_Repair013_73 (c1_depth c1_node c1_sign h r0_depth r0_node r0_sign : Int) : Prop := ((((¬ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ (shared_expr_Repair013_69 c1_node c1_sign h r0_depth r0_node r0_sign)) ∨ (shared_expr_Repair013_72 c1_depth c1_node c1_sign r0_depth r0_node r0_sign))
abbrev shared_expr_Repair013_74 (c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((¬ ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))))) ∧ (shared_expr_Repair013_73 c1_depth c1_node c1_sign h r0_depth r0_node r0_sign))
abbrev shared_expr_Repair013_75 (c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ∨ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (¬ (shared_expr_Repair013_66 c1_depth c1_kind h r0_kind))) ∨ (shared_expr_Repair013_74 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
theorem normalization_2092 (c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : ((formula_447 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (formula_369 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) ↔ ((shared_expr_Repair013_75 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_65 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) := (iff_congr (normalization_1662 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (normalization_2091 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_459 (c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : ((formula_447 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (formula_369 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) := by
  classical
  have ht := (normalized_345 ((r0_kind) ≤ (2 : Int)) ((r0_kind) ≤ (1 : Int)) ((c1_kind) ≤ (2 : Int)) ((c1_kind) ≤ (1 : Int)) ((c1_kind) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * h)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * h)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)) ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (0 : Int)) ((r0_sign) ≤ (0 : Int)) ((r0_sign) ≤ (-1 : Int)) ((c1_sign) ≤ (0 : Int)) ((c1_sign) ≤ (-1 : Int)) ((c1_node + ((-1 : Int) * r0_node)) ≤ (-1 : Int)) ((r0_sign) ≤ (2 : Int)) ((r0_sign) ≤ (1 : Int)) ((c1_sign) ≤ (2 : Int)) ((c1_sign) ≤ (1 : Int)) ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * r0_node)) ≤ (0 : Int)) ((c1_depth + ((-1 : Int) * r0_depth)) ≤ (-2 : Int)) (((r0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)) (((r0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2092 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) hn

abbrev shared_expr_Repair013_76 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∧ (formula_384 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ∧ (formula_369 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))
abbrev formula_492 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_76 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)

abbrev shared_expr_Repair013_77 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((formula_448 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (formula_492 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
abbrev formula_493 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_77 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)

theorem normalized_346 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2093 (c1_mode : Int) : (c1_mode ≤ (0 : Int)) ↔ ((c1_mode) ≤ (0 : Int)) := by
  omega

theorem normalization_2094 (c1_mode : Int) : (¬ (c1_mode ≤ (0 : Int))) ↔ (¬ ((c1_mode) ≤ (0 : Int))) := (not_congr (normalization_2093 c1_mode))

theorem normalization_2095 (c1_mode : Int) : (c1_mode ≥ (0 : Int)) ↔ (¬ ((c1_mode) ≤ (-1 : Int))) := by
  omega

theorem normalization_2096 (c1_mode : Int) : (¬ (c1_mode ≥ (0 : Int))) ↔ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) := (not_congr (normalization_2095 c1_mode))

theorem normalization_2097 (c1_group : Int) : (c1_group ≤ (1 : Int)) ↔ ((c1_group) ≤ (1 : Int)) := by
  omega

theorem normalization_2098 (c1_group : Int) : (¬ (c1_group ≤ (1 : Int))) ↔ (¬ ((c1_group) ≤ (1 : Int))) := (not_congr (normalization_2097 c1_group))

theorem normalization_2099 (c1_group : Int) : (c1_group ≥ (1 : Int)) ↔ (¬ ((c1_group) ≤ (0 : Int))) := by
  omega

theorem normalization_2100 (c1_group : Int) : (¬ (c1_group ≥ (1 : Int))) ↔ (¬ (¬ ((c1_group) ≤ (0 : Int)))) := (not_congr (normalization_2099 c1_group))

theorem normalization_2101 (c1_group : Int) : ((¬ (c1_group ≤ (1 : Int))) ∨ (¬ (c1_group ≥ (1 : Int)))) ↔ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) := (or_congr (normalization_2098 c1_group) (normalization_2100 c1_group))

theorem normalization_2102 (r0_kind : Int) : (r0_kind ≤ (1 : Int)) ↔ ((r0_kind) ≤ (1 : Int)) := by
  omega

theorem normalization_2103 (r0_kind : Int) : (¬ (r0_kind ≤ (1 : Int))) ↔ (¬ ((r0_kind) ≤ (1 : Int))) := (not_congr (normalization_2102 r0_kind))

theorem normalization_2104 (r0_kind : Int) : (r0_kind ≥ (1 : Int)) ↔ (¬ ((r0_kind) ≤ (0 : Int))) := by
  omega

theorem normalization_2105 (r0_kind : Int) : (¬ (r0_kind ≥ (1 : Int))) ↔ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) := (not_congr (normalization_2104 r0_kind))

theorem normalization_2106 (c1_level r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_2107 (c1_level r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int)))) := (not_congr (normalization_2106 c1_level r0_depth))

theorem normalization_2108 (c1_level r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_level)) ≥ (-1 : Int)) ↔ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (1 : Int)) := by
  omega

theorem normalization_2109 (c1_level r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_level)) ≥ (-1 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (1 : Int))) := (not_congr (normalization_2108 c1_level r0_depth))

abbrev shared_expr_Repair013_78 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (1 : Int))))
theorem normalization_2110 (c1_level r0_depth r0_kind r0_sign : Int) : (formula_370 c1_level r0_depth r0_kind r0_sign) ↔ (shared_expr_Repair013_78 c1_level r0_depth r0_kind r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2076 r0_sign) (or_congr (normalization_2107 c1_level r0_depth) (normalization_2109 c1_level r0_depth)))))

theorem normalization_2111 (c1_level r0_depth r0_kind r0_sign : Int) : (¬ (formula_370 c1_level r0_depth r0_kind r0_sign)) ↔ (¬ (shared_expr_Repair013_78 c1_level r0_depth r0_kind r0_sign)) := (not_congr (normalization_2110 c1_level r0_depth r0_kind r0_sign))

theorem normalization_2112 (c1_level r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2113 (c1_level r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2112 c1_level r0_depth))

theorem normalization_2114 (c1_level r0_depth : Int) : ((r0_depth + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ↔ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2115 (c1_level r0_depth : Int) : (¬ ((r0_depth + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) := (not_congr (normalization_2114 c1_level r0_depth))

abbrev shared_expr_Repair013_79 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))))
theorem normalization_2116 (c1_level r0_depth r0_kind r0_sign : Int) : (formula_371 c1_level r0_depth r0_kind r0_sign) ↔ (shared_expr_Repair013_79 c1_level r0_depth r0_kind r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2076 r0_sign) (or_congr (normalization_2113 c1_level r0_depth) (normalization_2115 c1_level r0_depth)))))

theorem normalization_2117 (c1_level r0_depth r0_kind r0_sign : Int) : (¬ (formula_371 c1_level r0_depth r0_kind r0_sign)) ↔ (¬ (shared_expr_Repair013_79 c1_level r0_depth r0_kind r0_sign)) := (not_congr (normalization_2116 c1_level r0_depth r0_kind r0_sign))

abbrev shared_expr_Repair013_80 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_78 c1_level r0_depth r0_kind r0_sign))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_79 c1_level r0_depth r0_kind r0_sign))))
theorem normalization_2118 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : (formula_372 c1_group c1_level r0_depth r0_kind r0_sign) ↔ (shared_expr_Repair013_80 c1_group c1_level r0_depth r0_kind r0_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_2111 c1_level r0_depth r0_kind r0_sign)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_2117 c1_level r0_depth r0_kind r0_sign)))

theorem normalization_2119 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : (¬ (formula_372 c1_group c1_level r0_depth r0_kind r0_sign)) ↔ (¬ (shared_expr_Repair013_80 c1_group c1_level r0_depth r0_kind r0_sign)) := (not_congr (normalization_2118 c1_group c1_level r0_depth r0_kind r0_sign))

theorem normalization_2120 (c1_group c1_level c1_mode r0_depth r0_kind r0_sign : Int) : ((¬ (c1_mode ≤ (0 : Int))) ∨ (¬ (c1_mode ≥ (0 : Int))) ∨ (¬ (formula_372 c1_group c1_level r0_depth r0_kind r0_sign))) ↔ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair013_80 c1_group c1_level r0_depth r0_kind r0_sign))) := (or_congr (normalization_2094 c1_mode) (or_congr (normalization_2096 c1_mode) (normalization_2119 c1_group c1_level r0_depth r0_kind r0_sign)))

theorem normalization_2121 (c1_group c1_level c1_mode r0_depth r0_kind r0_sign : Int) : (¬ ((¬ (c1_mode ≤ (0 : Int))) ∨ (¬ (c1_mode ≥ (0 : Int))) ∨ (¬ (formula_372 c1_group c1_level r0_depth r0_kind r0_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair013_80 c1_group c1_level r0_depth r0_kind r0_sign)))) := (not_congr (normalization_2120 c1_group c1_level c1_mode r0_depth r0_kind r0_sign))

theorem normalization_2122 (c1_mode : Int) : (c1_mode ≤ (1 : Int)) ↔ ((c1_mode) ≤ (1 : Int)) := by
  omega

theorem normalization_2123 (c1_mode : Int) : (¬ (c1_mode ≤ (1 : Int))) ↔ (¬ ((c1_mode) ≤ (1 : Int))) := (not_congr (normalization_2122 c1_mode))

theorem normalization_2124 (c1_mode : Int) : (c1_mode ≥ (1 : Int)) ↔ (¬ ((c1_mode) ≤ (0 : Int))) := by
  omega

theorem normalization_2125 (c1_mode : Int) : (¬ (c1_mode ≥ (1 : Int))) ↔ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) := (not_congr (normalization_2124 c1_mode))

abbrev shared_expr_Repair013_81 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))))
theorem normalization_2126 (c1_level r0_depth r0_kind r0_sign : Int) : (formula_373 c1_level r0_depth r0_kind r0_sign) ↔ (shared_expr_Repair013_81 c1_level r0_depth r0_kind r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2083 r0_sign) (or_congr (normalization_2113 c1_level r0_depth) (normalization_2115 c1_level r0_depth)))))

theorem normalization_2127 (c1_level r0_depth r0_kind r0_sign : Int) : (¬ (formula_373 c1_level r0_depth r0_kind r0_sign)) ↔ (¬ (shared_expr_Repair013_81 c1_level r0_depth r0_kind r0_sign)) := (not_congr (normalization_2126 c1_level r0_depth r0_kind r0_sign))

abbrev shared_expr_Repair013_82 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (1 : Int))))
theorem normalization_2128 (c1_level r0_depth r0_kind r0_sign : Int) : (formula_374 c1_level r0_depth r0_kind r0_sign) ↔ (shared_expr_Repair013_82 c1_level r0_depth r0_kind r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2083 r0_sign) (or_congr (normalization_2107 c1_level r0_depth) (normalization_2109 c1_level r0_depth)))))

theorem normalization_2129 (c1_level r0_depth r0_kind r0_sign : Int) : (¬ (formula_374 c1_level r0_depth r0_kind r0_sign)) ↔ (¬ (shared_expr_Repair013_82 c1_level r0_depth r0_kind r0_sign)) := (not_congr (normalization_2128 c1_level r0_depth r0_kind r0_sign))

abbrev shared_expr_Repair013_83 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ (shared_expr_Repair013_81 c1_level r0_depth r0_kind r0_sign))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_82 c1_level r0_depth r0_kind r0_sign))))
theorem normalization_2130 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : (formula_375 c1_group c1_level r0_depth r0_kind r0_sign) ↔ (shared_expr_Repair013_83 c1_group c1_level r0_depth r0_kind r0_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_2127 c1_level r0_depth r0_kind r0_sign)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_2129 c1_level r0_depth r0_kind r0_sign)))

theorem normalization_2131 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : (¬ (formula_375 c1_group c1_level r0_depth r0_kind r0_sign)) ↔ (¬ (shared_expr_Repair013_83 c1_group c1_level r0_depth r0_kind r0_sign)) := (not_congr (normalization_2130 c1_group c1_level r0_depth r0_kind r0_sign))

theorem normalization_2132 (c1_group c1_level c1_mode r0_depth r0_kind r0_sign : Int) : ((¬ (c1_mode ≤ (1 : Int))) ∨ (¬ (c1_mode ≥ (1 : Int))) ∨ (¬ (formula_375 c1_group c1_level r0_depth r0_kind r0_sign))) ↔ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair013_83 c1_group c1_level r0_depth r0_kind r0_sign))) := (or_congr (normalization_2123 c1_mode) (or_congr (normalization_2125 c1_mode) (normalization_2131 c1_group c1_level r0_depth r0_kind r0_sign)))

theorem normalization_2133 (c1_group c1_level c1_mode r0_depth r0_kind r0_sign : Int) : (¬ ((¬ (c1_mode ≤ (1 : Int))) ∨ (¬ (c1_mode ≥ (1 : Int))) ∨ (¬ (formula_375 c1_group c1_level r0_depth r0_kind r0_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair013_83 c1_group c1_level r0_depth r0_kind r0_sign)))) := (not_congr (normalization_2132 c1_group c1_level c1_mode r0_depth r0_kind r0_sign))

theorem normalization_2134 (c1_mode : Int) : (c1_mode ≤ (2 : Int)) ↔ ((c1_mode) ≤ (2 : Int)) := by
  omega

theorem normalization_2135 (c1_mode : Int) : (¬ (c1_mode ≤ (2 : Int))) ↔ (¬ ((c1_mode) ≤ (2 : Int))) := (not_congr (normalization_2134 c1_mode))

theorem normalization_2136 (c1_mode : Int) : (c1_mode ≥ (2 : Int)) ↔ (¬ ((c1_mode) ≤ (1 : Int))) := by
  omega

theorem normalization_2137 (c1_mode : Int) : (¬ (c1_mode ≥ (2 : Int))) ↔ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) := (not_congr (normalization_2136 c1_mode))

theorem normalization_2138 (r0_node : Int) : ((r0_node % (2 : Int)) ≤ (0 : Int)) ↔ (¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2139 (r0_node : Int) : (¬ ((r0_node % (2 : Int)) ≤ (0 : Int))) ↔ (¬ (¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2138 r0_node))

abbrev shared_expr_Repair013_84 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))))
theorem normalization_2140 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_376 c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_84 c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2076 r0_sign) (or_congr (normalization_2139 r0_node) (or_congr (normalization_2113 c1_level r0_depth) (normalization_2115 c1_level r0_depth))))))

theorem normalization_2141 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_376 c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_84 c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2140 c1_level r0_depth r0_kind r0_node r0_sign))

abbrev shared_expr_Repair013_85 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_84 c1_level r0_depth r0_kind r0_node r0_sign))))
theorem normalization_2142 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_377 c1_group c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_85 c1_group c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_2031 r0_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_2141 c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2143 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_377 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_85 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2142 c1_group c1_level r0_depth r0_kind r0_node r0_sign))

theorem normalization_2144 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : ((¬ (c1_mode ≤ (2 : Int))) ∨ (¬ (c1_mode ≥ (2 : Int))) ∨ (¬ (formula_377 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) ↔ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair013_85 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) := (or_congr (normalization_2135 c1_mode) (or_congr (normalization_2137 c1_mode) (normalization_2143 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2145 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : (¬ ((¬ (c1_mode ≤ (2 : Int))) ∨ (¬ (c1_mode ≥ (2 : Int))) ∨ (¬ (formula_377 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair013_85 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) := (not_congr (normalization_2144 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign))

theorem normalization_2146 (c1_mode : Int) : (c1_mode ≤ (3 : Int)) ↔ ((c1_mode) ≤ (3 : Int)) := by
  omega

theorem normalization_2147 (c1_mode : Int) : (¬ (c1_mode ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))) := (not_congr (normalization_2146 c1_mode))

theorem normalization_2148 (c1_mode : Int) : (c1_mode ≥ (3 : Int)) ↔ (¬ ((c1_mode) ≤ (2 : Int))) := by
  omega

theorem normalization_2149 (c1_mode : Int) : (¬ (c1_mode ≥ (3 : Int))) ↔ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) := (not_congr (normalization_2148 c1_mode))

theorem normalization_2150 (r0_node : Int) : ((r0_node % (2 : Int)) ≥ (1 : Int)) ↔ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2151 (r0_node : Int) : (¬ ((r0_node % (2 : Int)) ≥ (1 : Int))) ↔ (¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) := (not_congr (normalization_2150 r0_node))

abbrev shared_expr_Repair013_86 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))))
theorem normalization_2152 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_378 c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_86 c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2076 r0_sign) (or_congr (normalization_2151 r0_node) (or_congr (normalization_2113 c1_level r0_depth) (normalization_2115 c1_level r0_depth))))))

theorem normalization_2153 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_378 c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_86 c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2152 c1_level r0_depth r0_kind r0_node r0_sign))

abbrev shared_expr_Repair013_87 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_86 c1_level r0_depth r0_kind r0_node r0_sign))))
theorem normalization_2154 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_379 c1_group c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_87 c1_group c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_2031 r0_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_2153 c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2155 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_379 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_87 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2154 c1_group c1_level r0_depth r0_kind r0_node r0_sign))

theorem normalization_2156 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : ((¬ (c1_mode ≤ (3 : Int))) ∨ (¬ (c1_mode ≥ (3 : Int))) ∨ (¬ (formula_379 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) ↔ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair013_87 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) := (or_congr (normalization_2147 c1_mode) (or_congr (normalization_2149 c1_mode) (normalization_2155 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2157 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : (¬ ((¬ (c1_mode ≤ (3 : Int))) ∨ (¬ (c1_mode ≥ (3 : Int))) ∨ (¬ (formula_379 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair013_87 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) := (not_congr (normalization_2156 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign))

theorem normalization_2158 (c1_mode : Int) : (c1_mode ≤ (4 : Int)) ↔ ((c1_mode) ≤ (4 : Int)) := by
  omega

theorem normalization_2159 (c1_mode : Int) : (¬ (c1_mode ≤ (4 : Int))) ↔ (¬ ((c1_mode) ≤ (4 : Int))) := (not_congr (normalization_2158 c1_mode))

theorem normalization_2160 (c1_mode : Int) : (c1_mode ≥ (4 : Int)) ↔ (¬ ((c1_mode) ≤ (3 : Int))) := by
  omega

theorem normalization_2161 (c1_mode : Int) : (¬ (c1_mode ≥ (4 : Int))) ↔ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) := (not_congr (normalization_2160 c1_mode))

abbrev shared_expr_Repair013_88 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int)))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))))
theorem normalization_2162 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_380 c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_88 c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2083 r0_sign) (or_congr (normalization_2139 r0_node) (or_congr (normalization_2113 c1_level r0_depth) (normalization_2115 c1_level r0_depth))))))

theorem normalization_2163 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_380 c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_88 c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2162 c1_level r0_depth r0_kind r0_node r0_sign))

abbrev shared_expr_Repair013_89 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_88 c1_level r0_depth r0_kind r0_node r0_sign))))
theorem normalization_2164 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_381 c1_group c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_89 c1_group c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_2031 r0_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_2163 c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2165 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_381 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_89 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2164 c1_group c1_level r0_depth r0_kind r0_node r0_sign))

theorem normalization_2166 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : ((¬ (c1_mode ≤ (4 : Int))) ∨ (¬ (c1_mode ≥ (4 : Int))) ∨ (¬ (formula_381 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) ↔ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair013_89 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) := (or_congr (normalization_2159 c1_mode) (or_congr (normalization_2161 c1_mode) (normalization_2165 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2167 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : (¬ ((¬ (c1_mode ≤ (4 : Int))) ∨ (¬ (c1_mode ≥ (4 : Int))) ∨ (¬ (formula_381 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair013_89 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) := (not_congr (normalization_2166 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign))

theorem normalization_2168 (c1_mode : Int) : (c1_mode ≤ (5 : Int)) ↔ ((c1_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_2169 (c1_mode : Int) : (¬ (c1_mode ≤ (5 : Int))) ↔ (¬ ((c1_mode) ≤ (5 : Int))) := (not_congr (normalization_2168 c1_mode))

theorem normalization_2170 (c1_mode : Int) : (c1_mode ≥ (5 : Int)) ↔ (¬ ((c1_mode) ≤ (4 : Int))) := by
  omega

theorem normalization_2171 (c1_mode : Int) : (¬ (c1_mode ≥ (5 : Int))) ↔ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) := (not_congr (normalization_2170 c1_mode))

abbrev shared_expr_Repair013_90 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int)))))))) ∨ (¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∨ (¬ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))))
theorem normalization_2172 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_382 c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_90 c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2083 r0_sign) (or_congr (normalization_2151 r0_node) (or_congr (normalization_2113 c1_level r0_depth) (normalization_2115 c1_level r0_depth))))))

theorem normalization_2173 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_382 c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_90 c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2172 c1_level r0_depth r0_kind r0_node r0_sign))

abbrev shared_expr_Repair013_91 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (¬ ((¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int))))))) ∨ ((¬ ((¬ ((c1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_group) ≤ (0 : Int)))))) ∧ (¬ (shared_expr_Repair013_90 c1_level r0_depth r0_kind r0_node r0_sign))))
theorem normalization_2174 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (formula_383 c1_group c1_level r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_91 c1_group c1_level r0_depth r0_kind r0_node r0_sign) := (or_congr (and_congr (normalization_2101 c1_group) (normalization_2031 r0_kind)) (and_congr (not_congr (normalization_2101 c1_group)) (normalization_2173 c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2175 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : (¬ (formula_383 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) ↔ (¬ (shared_expr_Repair013_91 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) := (not_congr (normalization_2174 c1_group c1_level r0_depth r0_kind r0_node r0_sign))

theorem normalization_2176 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : ((¬ (c1_mode ≤ (5 : Int))) ∨ (¬ (c1_mode ≥ (5 : Int))) ∨ (¬ (formula_383 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) ↔ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_91 c1_group c1_level r0_depth r0_kind r0_node r0_sign))) := (or_congr (normalization_2169 c1_mode) (or_congr (normalization_2171 c1_mode) (normalization_2175 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))

theorem normalization_2177 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : (¬ ((¬ (c1_mode ≤ (5 : Int))) ∨ (¬ (c1_mode ≥ (5 : Int))) ∨ (¬ (formula_383 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) ↔ (¬ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_91 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) := (not_congr (normalization_2176 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign))

abbrev shared_expr_Repair013_92 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((¬ ((¬ ((c1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair013_80 c1_group c1_level r0_depth r0_kind r0_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (0 : Int)))) ∨ (¬ (shared_expr_Repair013_83 c1_group c1_level r0_depth r0_kind r0_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (1 : Int)))) ∨ (¬ (shared_expr_Repair013_85 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (3 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (2 : Int)))) ∨ (¬ (shared_expr_Repair013_87 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (4 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (3 : Int)))) ∨ (¬ (shared_expr_Repair013_89 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))) ∨ (¬ ((¬ ((c1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((c1_mode) ≤ (4 : Int)))) ∨ (¬ (shared_expr_Repair013_91 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))))
theorem normalization_2178 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : (formula_384 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_92 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) := (or_congr (normalization_2121 c1_group c1_level c1_mode r0_depth r0_kind r0_sign) (or_congr (normalization_2133 c1_group c1_level c1_mode r0_depth r0_kind r0_sign) (or_congr (normalization_2145 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (or_congr (normalization_2157 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (or_congr (normalization_2167 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (normalization_2177 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign))))))

abbrev shared_expr_Repair013_93 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_94 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (1 : Int))) ∧ ((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_95 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_93 c1_level r0_depth r0_kind r0_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_94 c1_level r0_depth r0_kind r0_sign)))
abbrev shared_expr_Repair013_96 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (1 : Int))) ∧ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_97 (c1_level r0_depth r0_kind r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_98 (c1_group c1_level r0_depth r0_kind r0_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_96 c1_level r0_depth r0_kind r0_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (shared_expr_Repair013_97 c1_level r0_depth r0_kind r0_sign)))
abbrev shared_expr_Repair013_99 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair013_100 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_99 c1_level r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_101 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair013_102 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_101 c1_level r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_103 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair013_104 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_103 c1_level r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_105 (c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ ((¬ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((c1_level + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∨ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))) ∧ ((¬ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-2 : Int))) ∧ ((((2 : Int) * (r0_node / (2 : Int))) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))))
abbrev shared_expr_Repair013_106 (c1_group c1_level r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_105 c1_level r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ (((c1_group) ≤ (1 : Int)) ∧ (¬ ((c1_group) ≤ (0 : Int))))) ∧ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))))
abbrev shared_expr_Repair013_107 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((((c1_mode) ≤ (0 : Int)) ∧ (¬ ((c1_mode) ≤ (-1 : Int)))) ∧ (shared_expr_Repair013_95 c1_group c1_level r0_depth r0_kind r0_sign)) ∨ ((((c1_mode) ≤ (1 : Int)) ∧ (¬ ((c1_mode) ≤ (0 : Int)))) ∧ (shared_expr_Repair013_98 c1_group c1_level r0_depth r0_kind r0_sign)) ∨ ((((c1_mode) ≤ (2 : Int)) ∧ (¬ ((c1_mode) ≤ (1 : Int)))) ∧ (shared_expr_Repair013_100 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) ∨ ((((c1_mode) ≤ (3 : Int)) ∧ (¬ ((c1_mode) ≤ (2 : Int)))) ∧ (shared_expr_Repair013_102 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) ∨ ((((c1_mode) ≤ (4 : Int)) ∧ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair013_104 c1_group c1_level r0_depth r0_kind r0_node r0_sign)) ∨ ((((c1_mode) ≤ (5 : Int)) ∧ (¬ ((c1_mode) ≤ (4 : Int)))) ∧ (shared_expr_Repair013_106 c1_group c1_level r0_depth r0_kind r0_node r0_sign)))
theorem normalization_2179 (c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign : Int) : ((formula_444 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) ↔ (formula_384 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) ↔ ((shared_expr_Repair013_107 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_92 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) := (iff_congr (normalization_1642 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (normalization_2178 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign))

abbrev shared_expr_Repair013_108 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair013_92 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair013_65 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))
theorem normalization_2180 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_492 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_108 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := (or_congr (and_congr (normalization_1683 c1_kind) (normalization_2178 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) (and_congr (not_congr (normalization_1683 c1_kind)) (normalization_2091 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))

abbrev shared_expr_Repair013_109 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair013_107 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair013_75 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))
abbrev shared_expr_Repair013_110 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((shared_expr_Repair013_109 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_108 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
theorem normalization_2181 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_493 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_110 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := (iff_congr (normalization_1663 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (normalization_2180 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))

-- Checked replay of monotonicity.
theorem replay_460 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_493 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := by
  classical
  have ht := (normalized_346 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair013_107 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (shared_expr_Repair013_92 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (shared_expr_Repair013_75 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (shared_expr_Repair013_65 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1685 c1_kind) (replay_319 c1_kind)
  have n1 : ((shared_expr_Repair013_107 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_92 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)) := by
    exact Iff.mp (normalization_2179 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (replay_458 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)
  have n2 : ((shared_expr_Repair013_75 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_65 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) := by
    exact Iff.mp (normalization_2092 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (replay_459 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2181 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) hn

abbrev shared_expr_Repair013_111 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((formula_492 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (formula_385 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
abbrev formula_494 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_111 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)

theorem normalized_347 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_112 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair013_65 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair013_92 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)))
theorem normalization_2182 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_385 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := (or_congr (and_congr (normalization_1682 c1_kind) (normalization_2091 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) (and_congr (not_congr (normalization_1682 c1_kind)) (normalization_2178 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign)))

abbrev shared_expr_Repair013_113 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((shared_expr_Repair013_108 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
theorem normalization_2183 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_494 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_113 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := (iff_congr (normalization_2180 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (normalization_2182 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_461 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_494 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := by
  classical
  have ht := (normalized_347 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Repair013_92 c1_group c1_level c1_mode r0_depth r0_kind r0_node r0_sign) (shared_expr_Repair013_65 c1_depth c1_kind c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
  have hn := ht
  exact Iff.mpr (normalization_2183 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) hn

abbrev shared_expr_Repair013_114 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((formula_448 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (formula_385 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
abbrev formula_495 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_114 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)

theorem normalized_348 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_115 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : Prop := ((shared_expr_Repair013_109 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
theorem normalization_2184 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_495 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) ↔ (shared_expr_Repair013_115 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := (iff_congr (normalization_1663 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (normalization_2182 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))

-- Checked replay of trans.
theorem replay_462 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign : Int) : (formula_495 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := by
  classical
  have ht := (normalized_348 (shared_expr_Repair013_109 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (shared_expr_Repair013_108 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
  have n0 : (shared_expr_Repair013_110 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := by
    exact Iff.mp (normalization_2181 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (replay_460 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)
  have n1 : (shared_expr_Repair013_113 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := by
    exact Iff.mp (normalization_2183 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (replay_461 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2184 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) hn

abbrev shared_expr_Repair013_116 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∧ (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) ∨ ((¬ (¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))))) ∧ (formula_385 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))
abbrev formula_496 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_116 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair013_117 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((formula_449 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_496 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
abbrev formula_497 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_117 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_349 (p0 p1 p2 p3 p4 p5 : Prop) : (((p0 ↔ (¬ p1)) ∧ (p2 ↔ p3) ∧ (p4 ↔ p5)) → (((p0 ∧ p2) ∨ ((¬ p0) ∧ p4)) ↔ (((¬ p1) ∧ p3) ∨ ((¬ (¬ p1)) ∧ p5)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_118 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (((¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) ∨ ((¬ (¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))))) ∧ (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))
theorem normalization_2185 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_496 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_118 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (and_congr (normalization_1673 r0_kind) (normalization_2023 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (and_congr (not_congr (normalization_1673 r0_kind)) (normalization_2182 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))

abbrev shared_expr_Repair013_119 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair013_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) ∨ ((¬ (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair013_109 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)))
abbrev shared_expr_Repair013_120 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((shared_expr_Repair013_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_118 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
theorem normalization_2186 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_497 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_120 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (iff_congr (normalization_1664 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2185 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of monotonicity.
theorem replay_463 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_497 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  classical
  have ht := (normalized_349 (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))) (shared_expr_Repair013_49 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (shared_expr_Repair013_109 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
  have n0 : ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1675 r0_kind) (replay_316 r0_kind)
  have n1 : (shared_expr_Repair013_55 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) := by
    exact Iff.mp (normalization_2025 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (replay_457 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)
  have n2 : (shared_expr_Repair013_115 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) := by
    exact Iff.mp (normalization_2184 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign) (replay_462 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)
  have hn := ht ⟨n0, n1, n2⟩
  exact Iff.mpr (normalization_2186 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

abbrev shared_expr_Repair013_121 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((formula_496 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_386 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
abbrev formula_498 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_121 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_350 (p0 p1 p2 : Prop) : ((((¬ p0) ∧ p1) ∨ ((¬ (¬ p0)) ∧ p2)) ↔ ((p0 ∧ p2) ∨ ((¬ p0) ∧ p1))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_122 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) ∨ ((¬ ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)))
theorem normalization_2187 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_386 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_122 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (and_congr (normalization_1672 r0_kind) (normalization_2182 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign)) (and_congr (not_congr (normalization_1672 r0_kind)) (normalization_2023 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)))

abbrev shared_expr_Repair013_123 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((shared_expr_Repair013_118 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_122 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
theorem normalization_2188 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_498 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_123 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (iff_congr (normalization_2185 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2187 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_464 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_498 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  classical
  have ht := (normalized_350 ((¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int))))) (shared_expr_Repair013_52 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (shared_expr_Repair013_112 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_kind r0_node r0_sign))
  have hn := ht
  exact Iff.mpr (normalization_2188 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

abbrev shared_expr_Repair013_124 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((formula_449 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_386 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
abbrev formula_499 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair013_124 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_351 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair013_125 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((shared_expr_Repair013_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_122 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
theorem normalization_2189 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_499 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair013_125 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (iff_congr (normalization_1664 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2187 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of trans.
theorem replay_465 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_499 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  classical
  have ht := (normalized_351 (shared_expr_Repair013_119 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair013_118 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair013_122 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
  have n0 : (shared_expr_Repair013_120 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
    exact Iff.mp (normalization_2186 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_463 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)
  have n1 : (shared_expr_Repair013_123 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
    exact Iff.mp (normalization_2188 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_464 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2189 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

end H4Formal.Generated.Repair
