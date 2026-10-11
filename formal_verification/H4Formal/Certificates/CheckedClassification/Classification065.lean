import H4Formal.Certificates.CheckedClassification.Classification064

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem propositional_1639 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3755 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_128 c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (propositional_1639 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (formula_128 c0_level r1_depth r1_kind r1_node r1_sign))

theorem propositional_1640 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3756 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) := by
  exact (propositional_1640 (c0_mode ≤ (3 : Int)) (c0_mode ≥ (3 : Int)) (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign))

theorem propositional_1641 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3757 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((formula_126 c0_level r1_depth r1_kind r1_node r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_1641 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

theorem propositional_1642 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3758 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_126 c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (propositional_1642 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (formula_126 c0_level r1_depth r1_kind r1_node r1_sign))

theorem propositional_1643 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3759 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) := by
  exact (propositional_1643 (c0_mode ≤ (2 : Int)) (c0_mode ≥ (2 : Int)) (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign))

-- Checked replay of unit-resolution.
theorem replay_3760 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) (i240 : (¬ (c0_mode ≥ (3 : Int)))) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_299 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim (i240 t0))))

-- Checked replay of unit-resolution.
theorem replay_3761 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i241 : (¬ (c0_mode ≥ (2 : Int)))) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_145 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_1113 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim (i241 t0))))

-- Checked replay of unit-resolution.
theorem replay_3762 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i241 : (¬ (c0_mode ≥ (2 : Int)))) (i90 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_140 c0_group c0_level r2_depth r2_kind r2_sign)))) (i89 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign)))) (i35 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) (i36 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_151 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) (i39 : (formula_152 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_147 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) := by
  exact (Or.elim (replay_198 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i39))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i90))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i89))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3761 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i241)))) (fun t3 => (Or.elim t3 (fun l4 => l4) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i35))) (fun t5 => (False.elim (t5 i36))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_3763 (c0_mode : Int) (i241 : (¬ (c0_mode ≥ (2 : Int)))) : (¬ (c0_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_288 c0_mode) (fun l0 => (False.elim (i241 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3764 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i241 : (¬ (c0_mode ≥ (2 : Int)))) (i90 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_140 c0_group c0_level r2_depth r2_kind r2_sign)))) (i89 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign)))) (i35 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) (i36 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_151 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) (i39 : (formula_152 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : False := by
  exact (Or.elim (replay_3206 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim ((replay_3762 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i241 i90 i89 i35 i36 i39) l0))) (fun t0 => (False.elim ((replay_3763 c0_mode i241) t0))))

abbrev shared_expr_Classification065_0 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((c0_mode ≥ (2 : Int)) ∨ (¬ (formula_152 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_151 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_140 c0_group c0_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))))
abbrev formula_1972 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Classification065_0 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_3765 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (formula_1972 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3764 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

abbrev shared_expr_Classification065_1 (c0_level h r1_depth r2_depth : Int) : Prop := (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
abbrev formula_1973 (c0_level h r1_depth r2_depth : Int) : Prop := (shared_expr_Classification065_1 c0_level h r1_depth r2_depth)

-- Checked replay of th-lemma.
theorem replay_3766 (c0_level h r1_depth r2_depth : Int) : (formula_1973 c0_level h r1_depth r2_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_3767 (c0_level r1_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3768 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (c0_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_301 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim (i242 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3769 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ (c0_mode ≥ (2 : Int))) := by
  exact (Or.elim (replay_300 c0_mode) (fun l0 => (False.elim (l0 (replay_3768 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i242)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3770 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ (c0_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_288 c0_mode) (fun l0 => (False.elim ((replay_3769 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3771 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_299 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_3770 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i242) t0))))

-- Checked replay of unit-resolution.
theorem replay_3772 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (c0_mode ≥ (1 : Int)) := by
  exact (Or.elim (replay_320 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim (i242 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3773 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ (c0_mode ≤ (0 : Int))) := by
  exact (Or.elim (replay_196 c0_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3772 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i242)))))

-- Checked replay of unit-resolution.
theorem replay_3774 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign))) := by
  exact (Or.elim (replay_286 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_3773 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i242) t0))))

-- Checked replay of unit-resolution.
theorem replay_3775 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_318 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_3769 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i242) t0))))

-- Checked replay of unit-resolution.
theorem replay_3776 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) := by
  exact (Or.elim (replay_183 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim (l0 i23))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3774 c0_group c0_level c0_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_sign i242)))) (fun t1 => (Or.elim t1 (fun l2 => l2) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3775 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i242)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_3771 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i242)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i40))) (fun t5 => (False.elim (t5 i41))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_3777 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (formula_125 c0_group c0_level r1_depth r1_kind r1_sign) := by
  exact (Or.elim (replay_298 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (fun l0 => (False.elim ((replay_3776 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i40 i41 i23 i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3778 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ (formula_124 c0_level r1_depth r1_kind r1_sign)) := by
  exact (Or.elim (replay_297 c0_group c0_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim (l0 (replay_3777 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i40 i41 i23 i242)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i30 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3779 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) := by
  exact (Or.elim (replay_335 c0_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim ((replay_3778 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i30 i40 i41 i23 i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3780 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (formula_143 c0_group c0_level r2_depth r2_kind r2_sign) := by
  exact (Or.elim (replay_294 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim (i242 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3781 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ (formula_142 c0_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_329 c0_group c0_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim (l0 (replay_3780 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i242)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i30 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3782 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) := by
  exact (Or.elim (replay_337 c0_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_3781 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i30 i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3783 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) := by
  exact (Or.elim (replay_3767 c0_level r1_depth r2_depth) (fun l0 => (False.elim (l0 (replay_3782 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i30 i242)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3779 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i30 i40 i41 i23 i242)))) (fun t1 => t1))))

theorem propositional_1644 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3784 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : ((formula_1523 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) ∨ (c0_group ≤ (0 : Int))) := by
  exact (propositional_1644 (c0_kind ≤ (2 : Int)) (c0_kind ≥ (2 : Int)) (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (c0_level ≤ (0 : Int)) (c0_level ≥ (0 : Int)) (c0_group ≤ (0 : Int)) (c0_group ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≤ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3785 (c0_group : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (c0_group ≥ (1 : Int)) := by
  exact (Or.elim (replay_2545 c0_group) (fun l0 => (False.elim (i30 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3786 (c0_group : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (¬ (c0_group ≤ (0 : Int))) := by
  exact (Or.elim (replay_2544 c0_group) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3785 c0_group i30)))))

-- Checked replay of unit-resolution.
theorem replay_3787 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (formula_1523 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) := by
  exact (Or.elim (replay_3784 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_3786 c0_group i30) t0))))

theorem propositional_1645 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p7))))) ∨ (¬ ((((¬ p10) ∨ (¬ p13)) ∧ ((¬ ((¬ p14) ∨ (¬ p15))) ∨ (¬ ((¬ p16) ∨ (¬ p17))))) ∨ ((¬ ((¬ p10) ∨ (¬ p13))) ∧ (¬ ((¬ p18) ∨ (¬ p19))))))) ∨ p4) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3788 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_1525 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (c0_group ≤ (0 : Int))) := by
  exact (propositional_1645 (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (c0_level ≤ (0 : Int)) (c0_level ≥ (0 : Int)) (c0_group ≤ (0 : Int)) (c0_group ≥ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_node ≤ (0 : Int)) ((h + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)) (c0_sign ≤ (2 : Int)) (c0_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3789 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (formula_1525 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := by
  exact (Or.elim (replay_3788 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_3786 c0_group i30) t0))))

-- Checked replay of unit-resolution.
theorem replay_3790 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (¬ (formula_1512 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  exact (Or.elim (replay_2521 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i178) (fun l0 => (False.elim (l0 (replay_3787 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign i30)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_3789 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i30)))))))

-- Checked replay of unit-resolution.
theorem replay_3791 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_2509 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (fun l0 => (False.elim ((replay_3790 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i178 i30) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3792 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) := by
  exact (Or.elim (replay_296 c0_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim ((replay_3778 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i30 i40 i41 i23 i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3793 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_3766 c0_level h r1_depth r2_depth) (fun l0 => (False.elim ((replay_3783 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i30 i40 i41 i23 i242) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3792 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i30 i40 i41 i23 i242)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3791 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i178 i30)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_3794 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) := by
  exact (Or.elim (replay_219 h r2_depth) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3793 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i30 i40 i41 i23 i242) t0))))

-- Checked replay of unit-resolution.
theorem replay_3795 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) := by
  exact (Or.elim (replay_218 h r2_depth r2_sign) (fun l0 => (False.elim (l0 i228))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3794 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i30 i40 i41 i23 i242)))) (fun t1 => (Or.elim t1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))))

-- Checked replay of unit-resolution.
theorem replay_3796 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ (r2_sign ≥ (2 : Int))) := by
  exact (Or.elim (replay_217 r2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3795 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i242)))))

-- Checked replay of unit-resolution.
theorem replay_3797 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))) := by
  exact (Or.elim (replay_205 r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3796 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i242) t0))))

-- Checked replay of unit-resolution.
theorem replay_3798 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) := by
  exact (Or.elim (replay_1102 c0_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_3781 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i30 i242) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_3799 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) := by
  exact (Or.elim (replay_204 r2_sign) (fun l0 => (False.elim (l0 (replay_3798 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i30 i242)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_3797 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i242)))))))

-- Checked replay of unit-resolution.
theorem replay_3800 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (r2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_203 r2_sign) (fun l0 => (False.elim ((replay_3799 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3801 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) := by
  exact (Or.elim (replay_384 r2_sign) (fun l0 => (False.elim (l0 i130))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_3797 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i242)))))))

-- Checked replay of unit-resolution.
theorem replay_3802 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : (r2_sign ≤ (0 : Int)) := by
  exact (Or.elim (replay_207 r2_sign) (fun l0 => (False.elim ((replay_3801 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i130 i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3803 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i40 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i41 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i242 : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))))) : False := by
  exact (Or.elim (replay_202 r2_sign) (fun l0 => (False.elim (l0 (replay_3802 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i130 i242)))) (fun t0 => (False.elim (t0 (replay_3800 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 i228 i30 i40 i41 i23 i242)))))

abbrev shared_expr_Classification065_2 (c0_group c0_level c0_mode h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) : Prop := (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ (formula_61 h r2_depth r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))))
abbrev formula_1974 (c0_group c0_level c0_mode h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Classification065_2 c0_group c0_level c0_mode h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign)

-- Checked replay of lemma.
theorem replay_3804 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) : (formula_1974 c0_group c0_level c0_mode h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3803 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178 (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inl q)))

-- Checked replay of unit-resolution.
theorem replay_3805 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i228 : (formula_61 h r2_depth r2_sign)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i26 : (¬ (c0_mode ≥ (4 : Int)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))) := by
  exact (Or.elim (replay_3804 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_sign i178) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i130))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i228))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (i30 l3))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i23))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_352 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign i26)))) (fun t5 => (False.elim (t5 (replay_349 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign i26)))))))))))))))

theorem propositional_1646 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3806 (c0_kind : Int) : ((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∨ (¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) := by
  exact (propositional_1646 (c0_kind ≤ (0 : Int)) (c0_kind ≥ (0 : Int)))

theorem propositional_1647 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p9) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3807 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_1512 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (c0_kind ≥ (0 : Int))) := by
  exact (propositional_1647 (c0_mode ≥ (6 : Int)) (c0_mode ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≤ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) (c0_kind ≤ (0 : Int)) (c0_kind ≥ (0 : Int)) (c0_level ≥ (1 : Int)) ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (c0_group ≤ (2 : Int)) (c0_group ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3808 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (c0_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_3807 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (fun l0 => (False.elim ((replay_3790 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i178 i30) l0))) (fun t0 => t0))

theorem propositional_1648 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p8) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3809 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_1512 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (c0_kind ≤ (0 : Int))) := by
  exact (propositional_1648 (c0_mode ≥ (6 : Int)) (c0_mode ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≤ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) (c0_kind ≤ (0 : Int)) (c0_kind ≥ (0 : Int)) (c0_level ≥ (1 : Int)) ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (c0_group ≤ (2 : Int)) (c0_group ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3810 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (c0_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_3809 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (fun l0 => (False.elim ((replay_3790 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i178 i30) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3811 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) (i178 : (formula_1517 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) := by
  exact (Or.elim (replay_3806 c0_kind) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3810 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i178 i30)))) (fun t1 => (False.elim (t1 (replay_3808 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h i178 i30)))))))

theorem propositional_1649 (p0 p1 : Prop) : ((p0 ↔ p1) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3812 (r1_mode r2_mode : Int) : (((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int)))) := by
  exact (propositional_1649 (r1_mode ≥ (4 : Int)) (r2_mode ≥ (4 : Int)))

abbrev shared_expr_Classification065_3 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (¬ ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_27 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))))
abbrev formula_1975 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification065_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)

theorem propositional_1650 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ p2)) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ ((((¬ p3) ∨ (¬ p4)) ∧ (¬ p4)) ∨ ((¬ ((¬ p3) ∨ (¬ p4))) ∧ (¬ p5)))))) ∨ ((¬ p0) ∧ p6))) ∨ p0 ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3813 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : ((formula_1975 r1_group r1_level r1_mode r2_group r2_level r2_mode) ∨ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∨ (r1_mode ≥ (4 : Int))) := by
  exact (propositional_1650 ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)) ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) (r1_mode ≥ (4 : Int)))

theorem propositional_1651 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ p2))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3814 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : ((formula_1975 r1_group r1_level r1_mode r2_group r2_level r2_mode) ∨ (¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∨ (formula_27 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := by
  exact (propositional_1651 ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) (formula_27 r1_group r1_level r1_mode r2_group r2_level r2_mode) (r1_mode ≥ (4 : Int)))

abbrev shared_expr_Classification065_4 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ (formula_27 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ∨ (formula_26 r1_group r1_mode r2_group r2_mode))
abbrev formula_1976 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification065_4 r1_group r1_level r1_mode r2_group r2_level r2_mode)

theorem propositional_1652 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ p2))) ∨ p0 ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3815 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_1976 r1_group r1_level r1_mode r2_group r2_level r2_mode) := by
  exact (propositional_1652 ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)) (formula_26 r1_group r1_mode r2_group r2_mode))

abbrev shared_expr_Classification065_5 (r1_group r1_mode r2_group r2_mode : Int) : Prop := ((¬ (formula_26 r1_group r1_mode r2_group r2_mode)) ∨ ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ∨ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int))))
abbrev formula_1977 (r1_group r1_mode r2_group r2_mode : Int) : Prop := (shared_expr_Classification065_5 r1_group r1_mode r2_group r2_mode)

theorem propositional_1653 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ p2)))) ∨ p0 ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3816 (r1_group r1_mode r2_group r2_mode : Int) : (formula_1977 r1_group r1_mode r2_group r2_mode) := by
  exact (propositional_1653 ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))

theorem propositional_1654 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3817 (r2_group : Int) : (((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int)))) ∨ (r2_group ≤ (2 : Int))) := by
  exact (propositional_1654 (r2_group ≤ (2 : Int)) (r2_group ≥ (2 : Int)))

abbrev shared_expr_Classification065_6 (r2_group : Int) : Prop := ((¬ ((¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int))))))) ∨ (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int))))))
abbrev formula_1978 (r2_group : Int) : Prop := (shared_expr_Classification065_6 r2_group)

theorem propositional_1655 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3818 (r2_group : Int) : (formula_1978 r2_group) := by
  exact (propositional_1655 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int)))))

theorem propositional_1656 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3819 (r2_group : Int) : (((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (r2_group ≤ (1 : Int))) := by
  exact (propositional_1656 (r2_group ≤ (1 : Int)) (r2_group ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_3820 (r1_group r2_group : Int) : ((r1_group ≤ (0 : Int)) ∨ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ∨ (¬ (r2_group ≤ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_3821 (r1_group : Int) : ((¬ (r1_group ≤ (0 : Int))) ∨ (r1_group ≤ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3822 (r1_group : Int) (i1 : (¬ (r1_group ≤ (1 : Int)))) : (¬ (r1_group ≤ (0 : Int))) := by
  exact (Or.elim (replay_3821 r1_group) (fun l0 => l0) (fun t0 => (False.elim (i1 t0))))

-- Checked replay of unit-resolution.
theorem replay_3823 (r1_group r2_group : Int) (i243 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i1 : (¬ (r1_group ≤ (1 : Int)))) : (¬ (r2_group ≤ (1 : Int))) := by
  exact (Or.elim (replay_3820 r1_group r2_group) (fun l0 => (False.elim ((replay_3822 r1_group i1) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i243 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3824 (r1_group r2_group : Int) (i243 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i1 : (¬ (r1_group ≤ (1 : Int)))) : ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) := by
  exact (Or.elim (replay_3819 r2_group) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3823 r1_group r2_group i243 i1) t0))))

-- Checked replay of unit-resolution.
theorem replay_3825 (r1_group r2_group : Int) (i243 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i1 : (¬ (r1_group ≤ (1 : Int)))) (i244 : ((¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int))))))) : (¬ ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int))))) := by
  exact (Or.elim (replay_3818 r2_group) (fun l0 => (False.elim (l0 i244))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3824 r1_group r2_group i243 i1)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3826 (r1_group r2_group : Int) (i243 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i1 : (¬ (r1_group ≤ (1 : Int)))) (i244 : ((¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int))))))) : (r2_group ≤ (2 : Int)) := by
  exact (Or.elim (replay_3817 r2_group) (fun l0 => (False.elim ((replay_3825 r1_group r2_group i243 i1 i244) l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_3827 (r1_group r2_group : Int) (i243 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i1 : (¬ (r1_group ≤ (1 : Int)))) (i244 : ((¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int))))))) : False := by
  classical
  have k0 := (replay_3826 r1_group r2_group i243 i1 i244)
  have k1 := i1
  have k2 := i243
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification065_7 (r1_group r2_group : Int) : Prop := (((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ∨ (r1_group ≤ (1 : Int)) ∨ (¬ ((¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_group ≤ (2 : Int))) ∨ (¬ (r2_group ≥ (2 : Int))))))))
abbrev formula_1979 (r1_group r2_group : Int) : Prop := (shared_expr_Classification065_7 r1_group r2_group)

-- Checked replay of lemma.
theorem replay_3828 (r1_group r2_group : Int) : (formula_1979 r1_group r2_group) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3827 r1_group r2_group (fun q => nc (Or.inl q)) (fun q => nc (Or.inr (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))))

-- Checked replay of th-lemma.
theorem replay_3829 (r1_group : Int) : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_3830 (c0_group r1_group : Int) : ((r1_group ≥ (2 : Int)) ∨ (c0_group ≤ (0 : Int)) ∨ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3831 (c0_group r1_group : Int) (i245 : (¬ (r1_group ≥ (2 : Int)))) (i246 : (¬ (c0_group ≤ (0 : Int)))) : ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3830 c0_group r1_group) (fun l0 => (False.elim (i245 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i246 l1))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_3832 (c0_group r1_group : Int) : ((r1_group ≤ (0 : Int)) ∨ (¬ (c0_group ≤ (1 : Int))) ∨ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_3833 (r1_group : Int) : ((¬ (r1_group ≤ (0 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3834 (r1_group : Int) (i245 : (¬ (r1_group ≥ (2 : Int)))) : ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))) := by
  exact (Or.elim (replay_15 r1_group) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i245 t0))))

-- Checked replay of unit-resolution.
theorem replay_3835 (r1_group : Int) (i245 : (¬ (r1_group ≥ (2 : Int)))) (i5 : ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) : (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) := by
  exact (Or.elim (replay_16 r1_group) (fun l0 => (False.elim (l0 i5))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_3834 r1_group i245)))))))

-- Checked replay of unit-resolution.
theorem replay_3836 (r1_group : Int) (i245 : (¬ (r1_group ≥ (2 : Int)))) (i5 : ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) : (r1_group ≥ (1 : Int)) := by
  exact (Or.elim (replay_17 r1_group) (fun l0 => (False.elim ((replay_3835 r1_group i245 i5) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3837 (r1_group : Int) (i245 : (¬ (r1_group ≥ (2 : Int)))) (i5 : ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) : (¬ (r1_group ≤ (0 : Int))) := by
  exact (Or.elim (replay_3833 r1_group) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3836 r1_group i245 i5)))))

-- Checked replay of unit-resolution.
theorem replay_3838 (c0_group r1_group : Int) (i245 : (¬ (r1_group ≥ (2 : Int)))) (i5 : ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) (i247 : (c0_group ≤ (1 : Int))) : ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3832 c0_group r1_group) (fun l0 => (False.elim ((replay_3837 r1_group i245 i5) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i247))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3839 (c0_group r1_group : Int) (i245 : (¬ (r1_group ≥ (2 : Int)))) (i5 : ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) (i246 : (¬ (c0_group ≤ (0 : Int)))) (i247 : (c0_group ≤ (1 : Int))) (i2 : ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) : False := by
  exact (Or.elim (replay_2 c0_group r1_group) (fun l0 => (False.elim (l0 i2))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3831 c0_group r1_group i245 i246)))) (fun t1 => (False.elim (t1 (replay_3838 c0_group r1_group i245 i5 i247)))))))

abbrev shared_expr_Classification065_8 (c0_group r1_group : Int) : Prop := ((r1_group ≥ (2 : Int)) ∨ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ∨ (c0_group ≤ (0 : Int)) ∨ (¬ (c0_group ≤ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))))
abbrev formula_1980 (c0_group r1_group : Int) : Prop := (shared_expr_Classification065_8 c0_group r1_group)

-- Checked replay of lemma.
theorem replay_3840 (c0_group r1_group : Int) : (formula_1980 c0_group r1_group) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3839 c0_group r1_group (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr q)))))) (fun q => nc (Or.inr (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

abbrev shared_expr_Classification065_9 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) ∨ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∨ (¬ (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode)))
abbrev formula_1981 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Classification065_9 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)

theorem propositional_1657 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Prop) : ((¬ ((p0 ∧ ((¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((p3 ∧ (¬ p4)) ∨ ((¬ p3) ∧ (¬ p5)))))) ∨ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ ((p3 ∧ (¬ p8)) ∨ ((¬ p3) ∧ (¬ p5)))))) ∨ (¬ ((¬ p9) ∨ (¬ p10) ∨ (¬ ((p3 ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16)))) ∨ ((¬ p3) ∧ (¬ p4)))))) ∨ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ ((p3 ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p19) ∨ (¬ p15) ∨ (¬ p16)))) ∨ ((¬ p3) ∧ (¬ p4)))))) ∨ (¬ ((¬ p20) ∨ (¬ p21) ∨ (¬ ((p3 ∧ (¬ p8)) ∨ ((¬ p3) ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p22) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16)))))))) ∨ (¬ ((¬ p23) ∨ (¬ p24) ∨ (¬ ((p3 ∧ (¬ p8)) ∨ ((¬ p3) ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p22) ∨ (¬ p19) ∨ (¬ p15) ∨ (¬ p16)))))))))) ∨ ((¬ p0) ∧ (¬ p25)))) ∨ p0 ∨ (¬ p25)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3841 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1981 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
  exact (propositional_1657 ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) (r1_mode ≤ (0 : Int)) (r1_mode ≥ (0 : Int)) ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) (formula_1658 c0_depth c0_kind c0_sign r1_level) ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) (r1_mode ≤ (1 : Int)) (r1_mode ≥ (1 : Int)) (formula_1660 c0_depth c0_kind c0_sign r1_level) (r1_mode ≤ (2 : Int)) (r1_mode ≥ (2 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ((c0_node % (2 : Int)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) (r1_mode ≤ (3 : Int)) (r1_mode ≥ (3 : Int)) ((c0_node % (2 : Int)) ≥ (1 : Int)) (r1_mode ≤ (4 : Int)) (r1_mode ≥ (4 : Int)) ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) (r1_mode ≤ (5 : Int)) (r1_mode ≥ (5 : Int)) (formula_0 c0_group c0_level c0_mode r1_group r1_level r1_mode))

abbrev shared_expr_Classification065_10 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ∨ (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ∨ (¬ (formula_1672 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))
abbrev formula_1982 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Classification065_10 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem propositional_1658 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 : Prop) : (p0 ∨ p1 ∨ (¬ ((p0 ∧ ((p2 ∧ ((¬ p3) ∨ (¬ p4) ∨ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ ((¬ ((¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17) ∨ (¬ p13))) ∨ (¬ (p7 ∨ p18 ∨ (¬ p19) ∨ (¬ p20) ∨ (¬ p21) ∨ (¬ p22))))))) ∨ (¬ ((¬ p23) ∨ (¬ p24) ∨ (¬ ((¬ ((¬ p16) ∨ (¬ p17) ∨ (¬ p25) ∨ (¬ p26))) ∨ (¬ (p27 ∨ (¬ p21) ∨ (¬ p22) ∨ (¬ p28))))))))) ∨ ((¬ p2) ∧ ((¬ ((¬ p29) ∨ (¬ p30) ∨ (¬ ((p31 ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p25)))) ∨ ((¬ p31) ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p25) ∨ (¬ p36) ∨ (¬ p37)))))))) ∨ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ ((p31 ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p36) ∨ (¬ p37) ∨ (¬ p28)))) ∨ ((¬ p31) ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p34) ∨ (¬ p35) ∨ (¬ p28)))))))) ∨ (¬ ((¬ p40) ∨ (¬ p41) ∨ (¬ ((p31 ∧ (¬ p3)) ∨ ((¬ p31) ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p25) ∨ (¬ p36) ∨ (¬ p37) ∨ (¬ p42)))))))) ∨ (¬ ((¬ p43) ∨ (¬ p44) ∨ (¬ ((p31 ∧ (¬ p3)) ∨ ((¬ p31) ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p25) ∨ (¬ p36) ∨ (¬ p37) ∨ (¬ p45)))))))) ∨ (¬ ((¬ p46) ∨ (¬ p47) ∨ (¬ ((p31 ∧ (¬ p3)) ∨ ((¬ p31) ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p36) ∨ (¬ p37) ∨ (¬ p28) ∨ (¬ p42)))))))) ∨ (¬ ((¬ p48) ∨ (¬ p49) ∨ (¬ ((p31 ∧ (¬ p3)) ∨ ((¬ p31) ∧ (¬ ((¬ p32) ∨ (¬ p33) ∨ (¬ p36) ∨ (¬ p37) ∨ (¬ p28) ∨ (¬ p45)))))))))))) ∨ ((¬ p0) ∧ p1)))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3842 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_1982 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (propositional_1658 ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))) ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) (c0_sign ≤ (2 : Int)) (c0_sign ≥ (2 : Int)) ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (c0_mode ≤ (2 : Int)) (c0_mode ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)) (c0_mode ≤ (3 : Int)) (c0_mode ≥ (3 : Int)) ((r1_node % (2 : Int)) ≥ (1 : Int)) (c0_mode ≤ (4 : Int)) (c0_mode ≥ (4 : Int)) (c0_mode ≤ (5 : Int)) (c0_mode ≥ (5 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3843 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i180 : ((formula_1693 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) : (((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ∨ (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) := by
  exact (Or.elim (replay_3842 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl (Or.inl l100))) (fun t100 => (Or.inl (Or.inr t100))))) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_2755 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i180)))))))

theorem propositional_1659 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ ((((¬ p5) ∨ (¬ p6)) ∧ ((((¬ p7) ∨ (¬ p8)) ∧ ((¬ p9) ∨ (¬ p10) ∨ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p11)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14))))))) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p17) ∨ (¬ p18)))))))) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ ((((¬ p19) ∨ (¬ p20)) ∧ (¬ p20)) ∨ ((¬ ((¬ p19) ∨ (¬ p20))) ∧ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ p13) ∨ (¬ p14)))))))))) ∨ p2) := by
  classical
  first | (by_cases case_p2 : p2 <;> simp [case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3844 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((formula_25 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ∨ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) := by
  exact (propositional_1659 (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int)) ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3845 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i248 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : (formula_25 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_3844 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim (i248 t0))))

-- Checked replay of unit-resolution.
theorem replay_3846 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i248 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) := by
  exact (Or.elim (replay_88 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3845 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i248)))))

-- Checked replay of unit-resolution.
theorem replay_3847 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_36 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i180 : ((formula_1693 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) (i248 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : (formula_1671 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
  exact (Or.elim (replay_3843 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i180) (fun l0 => (False.elim ((replay_3846 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10 i248) l0))) (fun t0 => t0))

end H4Formal.Generated.Classification
