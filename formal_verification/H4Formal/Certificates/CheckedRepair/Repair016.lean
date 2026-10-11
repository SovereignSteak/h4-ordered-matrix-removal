import H4Formal.Certificates.CheckedRepair.Repair015

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem propositional_401 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_542 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign))) ∨ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)) := by
  exact (propositional_401 (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (formula_569 c0_group c0_level r1_depth r1_kind r1_sign))

theorem propositional_402 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_543 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : ((¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ (formula_567 c0_level r1_depth r1_kind r1_sign))) := by
  exact (propositional_402 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (formula_567 c0_level r1_depth r1_kind r1_sign) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))

-- Checked replay of th-lemma.
theorem replay_544 (c2_level r1_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair016_0 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_580 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair016_0 c2_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair016_1 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (formula_580 c2_level r1_depth r1_kind r1_sign)) ∨ (¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))
abbrev formula_581 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair016_1 c2_level r1_depth r1_kind r1_sign)

theorem propositional_403 (p0 p1 p2 p3 p4 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_545 (c2_level r1_depth r1_kind r1_sign : Int) : (formula_581 c2_level r1_depth r1_kind r1_sign) := by
  exact (propositional_403 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_546 (c2_level r1_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_404 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_547 (c2_level r2_depth r2_kind r2_sign : Int) : ((formula_183 c2_level r2_depth r2_kind r2_sign) ∨ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) := by
  exact (propositional_404 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

theorem propositional_405 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_548 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∨ (¬ (formula_183 c2_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_405 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (formula_183 c2_level r2_depth r2_kind r2_sign) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

theorem propositional_406 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_549 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))) ∨ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign)) := by
  exact (propositional_406 (c2_mode ≤ (1 : Int)) (c2_mode ≥ (1 : Int)) (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))

theorem propositional_407 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_550 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_182 c2_group c2_level r2_depth r2_kind r2_sign))) ∨ (formula_182 c2_group c2_level r2_depth r2_kind r2_sign)) := by
  exact (propositional_407 (c2_mode ≤ (0 : Int)) (c2_mode ≥ (0 : Int)) (formula_182 c2_group c2_level r2_depth r2_kind r2_sign))

theorem propositional_408 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_551 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_182 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∨ (¬ (formula_180 c2_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_408 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (formula_180 c2_level r2_depth r2_kind r2_sign) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

abbrev shared_expr_Repair016_2 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))
abbrev formula_582 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair016_2 c2_level r1_depth r1_kind r1_sign)

abbrev shared_expr_Repair016_3 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (formula_582 c2_level r1_depth r1_kind r1_sign)) ∨ (¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))
abbrev formula_583 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair016_3 c2_level r1_depth r1_kind r1_sign)

theorem propositional_409 (p0 p1 p2 p3 p4 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_552 (c2_level r1_depth r1_kind r1_sign : Int) : (formula_583 c2_level r1_depth r1_kind r1_sign) := by
  exact (propositional_409 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

-- Checked replay of th-lemma.
theorem replay_553 (c2_level r1_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_410 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_554 (c2_level r2_depth r2_kind r2_sign : Int) : ((formula_184 c2_level r2_depth r2_kind r2_sign) ∨ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) := by
  exact (propositional_410 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

theorem propositional_411 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_555 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (formula_184 c2_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_411 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) (formula_184 c2_level r2_depth r2_kind r2_sign))

theorem propositional_412 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_556 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_182 c2_group c2_level r2_depth r2_kind r2_sign)) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (formula_181 c2_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_412 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)) (formula_181 c2_level r2_depth r2_kind r2_sign))

-- Checked replay of unit-resolution.
theorem replay_557 (c2_group c2_level r2_depth r2_kind r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) : (¬ (formula_182 c2_group c2_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_556 c2_group c2_level r2_depth r2_kind r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i34 l1))) (fun t1 => (False.elim (t1 i35))))))

-- Checked replay of unit-resolution.
theorem replay_558 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) : ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_182 c2_group c2_level r2_depth r2_kind r2_sign))) := by
  exact (Or.elim (replay_550 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_557 c2_group c2_level r2_depth r2_kind r2_sign i34 i35) t0))))

theorem propositional_413 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_559 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_413 (c2_mode ≤ (2 : Int)) (c2_mode ≥ (2 : Int)) (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_414 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_560 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (formula_186 c2_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_414 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_186 c2_level r2_depth r2_kind r2_node r2_sign))

-- Checked replay of unit-resolution.
theorem replay_561 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_560 c2_group c2_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i34 l1))) (fun t1 => (False.elim (t1 i36))))))

-- Checked replay of unit-resolution.
theorem replay_562 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) : ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_187 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_559 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_561 c2_group c2_level r2_depth r2_kind r2_node r2_sign i34 i36) t0))))

theorem propositional_415 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_563 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_415 (c2_mode ≤ (3 : Int)) (c2_mode ≥ (3 : Int)) (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_416 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_564 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (formula_188 c2_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_416 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_188 c2_level r2_depth r2_kind r2_node r2_sign))

-- Checked replay of unit-resolution.
theorem replay_565 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_564 c2_group c2_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i34 l1))) (fun t1 => (False.elim (t1 i37))))))

-- Checked replay of unit-resolution.
theorem replay_566 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) : ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_563 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_565 c2_group c2_level r2_depth r2_kind r2_node r2_sign i34 i37) t0))))

-- Checked replay of unit-resolution.
theorem replay_567 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign)))) := by
  exact (Or.elim (replay_215 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i17))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_558 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i34 i35)))) (fun t1 => (Or.elim t1 (fun l2 => l2) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_562 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i36)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_566 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i37)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i20))) (fun t5 => (False.elim (t5 i19))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_568 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (formula_185 c2_group c2_level r2_depth r2_kind r2_sign) := by
  exact (Or.elim (replay_549 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_567 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_569 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_184 c2_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_555 c2_group c2_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim (l0 (replay_568 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i34 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_570 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) := by
  exact (Or.elim (replay_554 c2_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_569 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_571 (c2_group c2_level c2_mode r1_depth r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i38 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) := by
  exact (Or.elim (replay_553 c2_level r1_depth r2_depth) (fun l0 => (False.elim (l0 (replay_570 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i38))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_572 (c2_level r1_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∨ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_417 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_573 (c2_level r2_depth r2_kind r2_sign : Int) : ((formula_184 c2_level r2_depth r2_kind r2_sign) ∨ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) := by
  exact (propositional_417 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_574 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)) := by
  exact (Or.elim (replay_573 c2_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_569 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_575 (c2_group c2_level c2_mode r1_depth r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i39 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)) := by
  exact (Or.elim (replay_572 c2_level r1_depth r2_depth) (fun l0 => (False.elim (l0 (replay_574 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i39 l1))) (fun t1 => t1))))

abbrev shared_expr_Repair016_4 (c2_group c2_level r1_depth r1_kind r1_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ (formula_580 c2_level r1_depth r1_kind r1_sign))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_582 c2_level r1_depth r1_kind r1_sign))))
abbrev formula_584 (c2_group c2_level r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair016_4 c2_group c2_level r1_depth r1_kind r1_sign)

theorem propositional_418 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6))) ∨ p0 ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_576 (c2_group c2_level r1_depth r1_kind r1_sign : Int) : ((formula_584 c2_group c2_level r1_depth r1_kind r1_sign) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (formula_582 c2_level r1_depth r1_kind r1_sign)) := by
  exact (propositional_418 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) (formula_582 c2_level r1_depth r1_kind r1_sign))

abbrev shared_expr_Repair016_5 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign : Int) : Prop := ((¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))) ∨ (¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))
abbrev formula_585 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign : Int) : Prop := (shared_expr_Repair016_5 c2_group c2_level c2_mode r1_depth r1_kind r1_sign)

theorem propositional_419 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_577 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign : Int) : (formula_585 c2_group c2_level c2_mode r1_depth r1_kind r1_sign) := by
  exact (propositional_419 (c2_mode ≤ (1 : Int)) (c2_mode ≥ (1 : Int)) (formula_584 c2_group c2_level r1_depth r1_kind r1_sign))

theorem propositional_420 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_578 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))) ∨ (c2_mode ≥ (1 : Int))) := by
  exact (propositional_420 (c2_mode ≤ (1 : Int)) (c2_mode ≥ (1 : Int)) (c2_group ≤ (1 : Int)) (c2_group ≥ (1 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_579 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (c2_mode ≥ (1 : Int)) := by
  exact (Or.elim (replay_578 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_567 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_580 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (c2_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_222 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_567 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_581 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i43 : ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)) := by
  exact (Or.elim (replay_577 c2_group c2_level c2_mode r1_depth r1_kind r1_sign) (fun l0 => (False.elim (l0 i43))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_580 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_579 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i35 i36 i37 i20 i19 i17)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_582 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i43 : ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (formula_582 c2_level r1_depth r1_kind r1_sign) := by
  exact (Or.elim (replay_576 c2_group c2_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim ((replay_581 c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign i34 i43 i35 i36 i37 i20 i19 i17) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i34 l1))) (fun t1 => (Or.elim t1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_583 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i41 : (r1_kind ≥ (1 : Int))) (i40 : (r1_kind ≤ (1 : Int))) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i38 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i39 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i42 : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i43 : ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))) (i35 : (formula_181 c2_level r2_depth r2_kind r2_sign)) (i36 : (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) (i37 : (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) (i20 : ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i19 : ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) (i17 : (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : False := by
  exact (Or.elim (replay_552 c2_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim (l0 (replay_582 c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign i34 i43 i35 i36 i37 i20 i19 i17)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i40))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i41))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i42))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_571 c2_group c2_level c2_mode r1_depth r2_depth r2_kind r2_node r2_sign i34 i38 i35 i36 i37 i20 i19 i17)))) (fun t4 => (False.elim (t4 (replay_575 c2_group c2_level c2_mode r1_depth r2_depth r2_kind r2_node r2_sign i34 i39 i35 i36 i37 i20 i19 i17)))))))))))))

abbrev shared_expr_Repair016_6 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∨ (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))) ∨ (¬ (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_191 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_193 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ (¬ (formula_186 c2_level r2_depth r2_kind r2_node r2_sign)) ∨ (¬ (formula_181 c2_level r2_depth r2_kind r2_sign)))
abbrev formula_586 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair016_6 c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_584 (c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_586 c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_583 c2_group c2_level c2_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))

-- Checked replay of th-lemma.
theorem replay_585 (c0_level r1_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_421 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_586 (c0_level r1_depth r1_kind r1_sign : Int) : ((formula_568 c0_level r1_depth r1_kind r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) := by
  exact (propositional_421 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)))

theorem propositional_422 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_587 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : ((¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_568 c0_level r1_depth r1_kind r1_sign))) := by
  exact (propositional_422 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) (formula_568 c0_level r1_depth r1_kind r1_sign))

theorem propositional_423 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_588 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_577 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (c0_mode ≥ (5 : Int))) := by
  exact (propositional_423 (c0_mode ≤ (5 : Int)) (c0_mode ≥ (5 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≥ (1 : Int)))

theorem propositional_424 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_589 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_575 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (c0_mode ≥ (4 : Int))) := by
  exact (propositional_424 (c0_mode ≤ (4 : Int)) (c0_mode ≥ (4 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_590 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) (i44 : (¬ (c0_mode ≥ (4 : Int)))) : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_575 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_589 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim (i44 t0))))

-- Checked replay of unit-resolution.
theorem replay_591 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i49 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign)))) (i46 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)))) (i47 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i48 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i45 : (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) : (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_577 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) := by
  exact (Or.elim (replay_541 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim (l0 i45))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i49))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i46))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i47))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i48))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_590 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign i44)))) (fun t5 => t5))))))))))))

-- Checked replay of th-lemma.
theorem replay_592 (c0_mode : Int) : ((c0_mode ≥ (4 : Int)) ∨ (¬ (c0_mode ≥ (5 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_593 (c0_mode : Int) (i44 : (¬ (c0_mode ≥ (4 : Int)))) : (¬ (c0_mode ≥ (5 : Int))) := by
  exact (Or.elim (replay_592 c0_mode) (fun l0 => (False.elim (i44 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_594 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i49 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign)))) (i46 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)))) (i47 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i48 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i45 : (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) : False := by
  exact (Or.elim (replay_588 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_591 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign i44 i49 i46 i47 i48 i45) l0))) (fun t0 => (False.elim ((replay_593 c0_mode i44) t0))))

abbrev shared_expr_Repair016_7 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((c0_mode ≥ (4 : Int)) ∨ (¬ (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign)))))
abbrev formula_587 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair016_7 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)

-- Checked replay of lemma.
theorem replay_595 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (formula_587 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_594 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

-- Checked replay of th-lemma.
theorem replay_596 (c0_mode : Int) : ((c0_mode ≥ (3 : Int)) ∨ (¬ (c0_mode ≥ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_597 (c0_mode : Int) : ((c0_mode ≥ (2 : Int)) ∨ (¬ (c0_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_598 (c0_mode : Int) : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_425 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p8))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_599 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign))) ∨ (c0_mode ≤ (1 : Int))) := by
  exact (propositional_425 (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)))

abbrev shared_expr_Repair016_8 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))))
abbrev formula_588 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair016_8 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)

theorem propositional_426 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_600 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (formula_588 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) := by
  exact (propositional_426 ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign))) ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign))) ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))

theorem propositional_427 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_601 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_427 (c0_mode ≤ (3 : Int)) (c0_mode ≥ (3 : Int)) (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_428 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_602 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_71 c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_428 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_71 c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_429 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_603 (c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_71 c0_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_429 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_604 (c0_level r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_605 (c0_level r2_depth : Int) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_604 c0_level r2_depth) (fun l0 => (False.elim (l0 i51))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_606 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (formula_71 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_603 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim ((replay_605 c0_level r2_depth i51) t0))))

-- Checked replay of unit-resolution.
theorem replay_607 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_602 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_606 c0_level r2_depth r2_kind r2_node r2_sign i51)))))))

-- Checked replay of unit-resolution.
theorem replay_608 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_601 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_607 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i51) t0))))

theorem propositional_430 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_609 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_430 (c0_mode ≤ (2 : Int)) (c0_mode ≥ (2 : Int)) (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_431 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_610 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_69 c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_431 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_69 c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_432 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_611 (c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_69 c0_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_432 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_612 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (formula_69 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_611 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim ((replay_605 c0_level r2_depth i51) t0))))

-- Checked replay of unit-resolution.
theorem replay_613 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_610 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_612 c0_level r2_depth r2_kind r2_node r2_sign i51)))))))

-- Checked replay of unit-resolution.
theorem replay_614 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_609 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_613 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i51) t0))))

theorem propositional_433 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_615 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_433 (c0_mode ≤ (4 : Int)) (c0_mode ≥ (4 : Int)) (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_434 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_616 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_73 c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_434 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_73 c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_435 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_617 (c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_73 c0_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_435 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_618 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (formula_73 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_617 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim ((replay_605 c0_level r2_depth i51) t0))))

-- Checked replay of unit-resolution.
theorem replay_619 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_616 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_618 c0_level r2_depth r2_kind r2_node r2_sign i51)))))))

-- Checked replay of unit-resolution.
theorem replay_620 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_615 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_619 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i51) t0))))

theorem propositional_436 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_621 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_436 (c0_mode ≤ (5 : Int)) (c0_mode ≥ (5 : Int)) (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_437 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_622 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_75 c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_437 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_75 c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_438 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_623 (c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_75 c0_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_438 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_624 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (formula_75 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_623 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim ((replay_605 c0_level r2_depth i51) t0))))

-- Checked replay of unit-resolution.
theorem replay_625 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_622 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_624 c0_level r2_depth r2_kind r2_node r2_sign i51)))))))

-- Checked replay of unit-resolution.
theorem replay_626 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_621 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_625 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i51) t0))))

theorem propositional_439 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_627 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign))) ∨ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign)) := by
  exact (propositional_439 (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (formula_65 c0_group c0_level r2_depth r2_kind r2_sign))

theorem propositional_440 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_628 (c0_group c0_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_64 c0_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_440 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) (formula_64 c0_level r2_depth r2_kind r2_sign))

theorem propositional_441 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_629 (c0_level r2_depth r2_kind r2_sign : Int) : ((formula_64 c0_level r2_depth r2_kind r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_441 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))

end H4Formal.Generated.Repair
