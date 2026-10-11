import H4Formal.Certificates.CheckedRepair.Repair067

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of th-lemma.
theorem replay_3950 (r2_mode : Int) : ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_3951 (r2_mode : Int) : ((r2_mode ≥ (3 : Int)) ∨ (¬ (r2_mode ≥ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1612 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3952 (c2_depth c2_kind c2_node c2_sign r0_group r0_level r0_mode : Int) : (((¬ (r0_mode ≤ (5 : Int))) ∨ (¬ (r0_mode ≥ (5 : Int))) ∨ (¬ (formula_1601 c2_depth c2_kind c2_node c2_sign r0_group r0_level))) ∨ (formula_1601 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) := by
  exact (propositional_1612 (r0_mode ≤ (5 : Int)) (r0_mode ≥ (5 : Int)) (formula_1601 c2_depth c2_kind c2_node c2_sign r0_group r0_level))

theorem propositional_1613 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3953 (c2_depth c2_kind c2_node c2_sign r0_group r0_level : Int) : ((¬ (formula_1601 c2_depth c2_kind c2_node c2_sign r0_group r0_level)) ∨ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))) ∨ (¬ (formula_1600 c2_depth c2_kind c2_node c2_sign r0_level))) := by
  exact (propositional_1613 ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) (formula_1600 c2_depth c2_kind c2_node c2_sign r0_level))

theorem propositional_1614 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3954 (c2_depth c2_kind c2_node c2_sign r0_level : Int) : ((formula_1600 c2_depth c2_kind c2_node c2_sign r0_level) ∨ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  exact (propositional_1614 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((r0_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c2_node % (2 : Int)) ≥ (1 : Int)))

theorem propositional_1615 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3955 (c2_sign : Int) : (((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))) ∨ (c2_sign ≤ (0 : Int))) := by
  exact (propositional_1615 (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)))

abbrev shared_expr_Repair068_0 (c2_sign : Int) : Prop := ((¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))
abbrev formula_1882 (c2_sign : Int) : Prop := (shared_expr_Repair068_0 c2_sign)

theorem propositional_1616 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3956 (c2_sign : Int) : (formula_1882 c2_sign) := by
  exact (propositional_1616 ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))) ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_3957 (c2_sign : Int) (i174 : ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) (i224 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) := by
  exact (Or.elim (replay_3956 c2_sign) (fun l0 => (False.elim (l0 i224))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 i174))))))

-- Checked replay of unit-resolution.
theorem replay_3958 (c2_sign : Int) (i174 : ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) (i224 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : (c2_sign ≤ (0 : Int)) := by
  exact (Or.elim (replay_3955 c2_sign) (fun l0 => (False.elim ((replay_3957 c2_sign i174 i224) l0))) (fun t0 => t0))

abbrev shared_expr_Repair068_1 (c2_sign : Int) : Prop := ((¬ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))
abbrev formula_1883 (c2_sign : Int) : Prop := (shared_expr_Repair068_1 c2_sign)

theorem propositional_1617 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3959 (c2_sign : Int) : (formula_1883 c2_sign) := by
  exact (propositional_1617 ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_3960 (c2_sign : Int) (i174 : ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) (i225 : ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) := by
  exact (Or.elim (replay_3959 c2_sign) (fun l0 => (False.elim (l0 i225))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 i174))))))

-- Checked replay of unit-resolution.
theorem replay_3961 (c2_sign : Int) (i174 : ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) (i225 : ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : (c2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_2609 c2_sign) (fun l0 => (False.elim ((replay_3960 c2_sign i174 i225) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3962 (c2_sign : Int) (i174 : ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) (i224 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) (i225 : ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : False := by
  exact (Or.elim (replay_2605 c2_sign) (fun l0 => (False.elim (l0 (replay_3958 c2_sign i174 i224)))) (fun t0 => (False.elim (t0 (replay_3961 c2_sign i174 i225)))))

abbrev shared_expr_Repair068_2 (c2_sign : Int) : Prop := ((¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) ∨ (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))))
abbrev formula_1884 (c2_sign : Int) : Prop := (shared_expr_Repair068_2 c2_sign)

-- Checked replay of lemma.
theorem replay_3963 (c2_sign : Int) : (formula_1884 c2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3962 c2_sign (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))))

-- Checked replay of unit-resolution.
theorem replay_3964 (c2_sign : Int) (i226 : (c2_sign ≥ (2 : Int))) : (c2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_2604 c2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 i226))))

-- Checked replay of unit-resolution.
theorem replay_3965 (c2_sign : Int) (i226 : (c2_sign ≥ (2 : Int))) : (¬ (c2_sign ≤ (0 : Int))) := by
  exact (Or.elim (replay_2605 c2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3964 c2_sign i226)))))

-- Checked replay of unit-resolution.
theorem replay_3966 (c2_sign : Int) (i226 : (c2_sign ≥ (2 : Int))) : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))) := by
  exact (Or.elim (replay_3955 c2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3965 c2_sign i226) t0))))

theorem propositional_1618 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3967 (c2_sign : Int) : (((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ∨ (c2_sign ≤ (1 : Int))) := by
  exact (propositional_1618 (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_3968 (c2_sign : Int) : ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3969 (c2_sign : Int) (i226 : (c2_sign ≥ (2 : Int))) : (¬ (c2_sign ≤ (1 : Int))) := by
  exact (Or.elim (replay_3968 c2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 i226))))

-- Checked replay of unit-resolution.
theorem replay_3970 (c2_sign : Int) (i226 : (c2_sign ≥ (2 : Int))) : ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) := by
  exact (Or.elim (replay_3967 c2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3969 c2_sign i226) t0))))

-- Checked replay of unit-resolution.
theorem replay_3971 (c2_sign : Int) (i226 : (c2_sign ≥ (2 : Int))) (i227 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) : False := by
  exact (Or.elim (replay_2597 c2_sign) (fun l0 => (False.elim (l0 i227))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3966 c2_sign i226)))) (fun t1 => (False.elim (t1 (replay_3970 c2_sign i226)))))))

-- Checked replay of lemma.
theorem replay_3972 (c2_sign : Int) : ((¬ (c2_sign ≥ (2 : Int))) ∨ (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3971 c2_sign (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr q))))

theorem propositional_1619 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3973 (c2_depth h : Int) : (((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ∨ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  exact (propositional_1619 ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_3974 (c2_depth h r2_level : Int) (i229 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i230 : ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i228 : (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) : False := by
  classical
  have k0 := i228
  have k1 := i229
  have k2 := i230
  first | omega | grind (splits := 40)

-- Checked replay of lemma.
theorem replay_3975 (c2_depth h r2_level : Int) : ((¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3974 c2_depth h r2_level (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))) (Classical.byContradiction (fun q => nc (Or.inl q))) (fun q => nc (Or.inr (Or.inl q))))

-- Checked replay of th-lemma.
theorem replay_3976 (c2_depth r2_level : Int) : ((¬ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1620 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3977 (c2_depth c2_kind c2_sign r2_level : Int) : ((formula_196 c2_depth c2_kind c2_sign r2_level) ∨ ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) := by
  exact (propositional_1620 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))

theorem propositional_1621 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3978 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_203 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ∨ (formula_203 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (propositional_1621 (r2_mode ≤ (3 : Int)) (r2_mode ≥ (3 : Int)) (formula_203 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem propositional_1622 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))) ∨ ((¬ p0) ∧ (¬ p7)))) ∨ p0 ∨ (¬ p7)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3979 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : ((¬ (formula_203 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ (formula_196 c2_depth c2_kind c2_sign r2_level))) := by
  exact (propositional_1622 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((c2_node % (2 : Int)) ≥ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) (formula_196 c2_depth c2_kind c2_sign r2_level))

-- Checked replay of unit-resolution.
theorem replay_3980 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : (formula_196 c2_depth c2_kind c2_sign r2_level)) : (¬ (formula_203 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_3979 c2_depth c2_kind c2_node c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i232 l1))) (fun t1 => (False.elim (t1 i231))))))

-- Checked replay of unit-resolution.
theorem replay_3981 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : (formula_196 c2_depth c2_kind c2_sign r2_level)) : ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_203 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_3978 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_3980 c2_depth c2_kind c2_node c2_sign r2_group r2_level i232 i231) t0))))

theorem propositional_1623 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3982 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_201 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ∨ (formula_201 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (propositional_1623 (r2_mode ≤ (2 : Int)) (r2_mode ≥ (2 : Int)) (formula_201 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem propositional_1624 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))) ∨ ((¬ p0) ∧ (¬ p7)))) ∨ p0 ∨ (¬ p7)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3983 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : ((¬ (formula_201 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ (formula_196 c2_depth c2_kind c2_sign r2_level))) := by
  exact (propositional_1624 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((c2_node % (2 : Int)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) (formula_196 c2_depth c2_kind c2_sign r2_level))

-- Checked replay of unit-resolution.
theorem replay_3984 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : (formula_196 c2_depth c2_kind c2_sign r2_level)) : (¬ (formula_201 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_3983 c2_depth c2_kind c2_node c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i232 l1))) (fun t1 => (False.elim (t1 i231))))))

-- Checked replay of unit-resolution.
theorem replay_3985 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : (formula_196 c2_depth c2_kind c2_sign r2_level)) : ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_201 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_3982 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_3984 c2_depth c2_kind c2_node c2_sign r2_group r2_level i232 i231) t0))))

-- Checked replay of unit-resolution.
theorem replay_3986 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : (formula_196 c2_depth c2_kind c2_sign r2_level)) (i235 : ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_197 c2_depth c2_kind c2_sign r2_group r2_level)))) (i234 : ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_199 c2_depth c2_kind c2_sign r2_group r2_level)))) (i236 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_205 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i237 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_207 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i233 : (formula_208 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : False := by
  exact (Or.elim (replay_3948 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (False.elim (l0 i233))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i235))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i234))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3985 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i232 i231)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_3981 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i232 i231)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i236))) (fun t5 => (False.elim (t5 i237))))))))))))))

abbrev shared_expr_Repair068_3 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ (formula_196 c2_depth c2_kind c2_sign r2_level)) ∨ (¬ (formula_208 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) ∨ (¬ ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_199 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_197 c2_depth c2_kind c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_205 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_207 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))
abbrev formula_1885 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair068_3 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)

-- Checked replay of lemma.
theorem replay_3987 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1885 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3986 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

theorem propositional_1625 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3988 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_207 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ∨ (r2_mode ≥ (5 : Int))) := by
  exact (propositional_1625 (r2_mode ≤ (5 : Int)) (r2_mode ≥ (5 : Int)) (r2_group ≤ (1 : Int)) (r2_group ≥ (1 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((c2_node % (2 : Int)) ≥ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_3989 (r2_mode : Int) : ((r2_mode ≥ (4 : Int)) ∨ (¬ (r2_mode ≥ (5 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3990 (r2_mode : Int) (i238 : (¬ (r2_mode ≥ (4 : Int)))) : (¬ (r2_mode ≥ (5 : Int))) := by
  exact (Or.elim (replay_3989 r2_mode) (fun l0 => (False.elim (i238 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3991 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i238 : (¬ (r2_mode ≥ (4 : Int)))) : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_207 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_3988 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_3990 r2_mode i238) t0))))

abbrev shared_expr_Repair068_4 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ (formula_210 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)) ∨ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (formula_208 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode))
abbrev formula_1886 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair068_4 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)

theorem propositional_1626 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ p6) ∨ (¬ p7)))))))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3992 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_1886 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := by
  exact (propositional_1626 ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) (formula_208 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) ((r2_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ((r2_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ((r2_group + ((-1 : Int) * c2_group)) ≤ (0 : Int)) ((r2_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair068_5 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) ∨ (formula_210 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ∨ (¬ (formula_211 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)))
abbrev formula_1887 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair068_5 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem propositional_1627 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 : Prop) : (p0 ∨ p1 ∨ (¬ ((p0 ∧ ((p2 ∧ ((((¬ p3) ∨ (¬ p4)) ∧ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10))) ∨ ((¬ ((¬ p3) ∨ (¬ p4))) ∧ ((¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ ((¬ ((¬ p13) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17))) ∨ (¬ ((¬ p18) ∨ (¬ p19) ∨ (¬ p20) ∨ (¬ p21) ∨ (¬ p22) ∨ (¬ p23) ∨ (¬ p17))) ∨ (¬ (p18 ∨ p24 ∨ (¬ p25) ∨ (¬ p26) ∨ (¬ p27) ∨ (¬ p28))))))) ∨ (¬ ((¬ p29) ∨ (¬ p30) ∨ (¬ ((¬ ((¬ p15) ∨ (¬ p16) ∨ (¬ p31) ∨ (¬ p32))) ∨ (¬ (p33 ∨ (¬ p27) ∨ (¬ p28) ∨ (¬ p34))))))))))) ∨ ((¬ p2) ∧ ((¬ ((¬ p35) ∨ (¬ p36) ∨ (¬ ((p37 ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p31) ∨ (¬ p40) ∨ (¬ p41)))) ∨ ((¬ p37) ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p31) ∨ (¬ p42) ∨ (¬ p43)))))))) ∨ (¬ ((¬ p44) ∨ (¬ p45) ∨ (¬ ((p37 ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p34) ∨ (¬ p42) ∨ (¬ p43)))) ∨ ((¬ p37) ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p34) ∨ (¬ p40) ∨ (¬ p41)))))))) ∨ (¬ ((¬ p46) ∨ (¬ p47) ∨ (¬ ((p37 ∧ (¬ p3)) ∨ ((¬ p37) ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p31) ∨ (¬ p48) ∨ (¬ p42) ∨ (¬ p43)))))))) ∨ (¬ ((¬ p49) ∨ (¬ p50) ∨ (¬ ((p37 ∧ (¬ p3)) ∨ ((¬ p37) ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p31) ∨ (¬ p51) ∨ (¬ p42) ∨ (¬ p43)))))))) ∨ (¬ ((¬ p52) ∨ (¬ p53) ∨ (¬ ((p37 ∧ (¬ p3)) ∨ ((¬ p37) ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p34) ∨ (¬ p48) ∨ (¬ p42) ∨ (¬ p43)))))))) ∨ (¬ ((¬ p54) ∨ (¬ p55) ∨ (¬ ((p37 ∧ (¬ p3)) ∨ ((¬ p37) ∧ (¬ ((¬ p38) ∨ (¬ p39) ∨ (¬ p34) ∨ (¬ p51) ∨ (¬ p42) ∨ (¬ p43)))))))))))) ∨ ((¬ p0) ∧ p1)))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3993 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1887 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (propositional_1627 ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) (formula_210 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) (c2_mode ≤ (0 : Int)) (c2_mode ≥ (0 : Int)) ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) (c2_mode ≤ (1 : Int)) (c2_mode ≥ (1 : Int)) (c2_mode ≤ (2 : Int)) (c2_mode ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)) (c2_mode ≤ (3 : Int)) (c2_mode ≥ (3 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)) (c2_mode ≤ (4 : Int)) (c2_mode ≥ (4 : Int)) (c2_mode ≤ (5 : Int)) (c2_mode ≥ (5 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3994 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) ∨ (formula_210 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode)) := by
  exact (Or.elim (replay_3993 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl (Or.inl l100))) (fun t100 => (Or.inl (Or.inr t100))))) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_212 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i15)))))))

abbrev shared_expr_Repair068_6 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (formula_179 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ∨ (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))
abbrev formula_1888 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair068_6 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)

theorem propositional_1628 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : ((¬ ((p0 ∧ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ ((¬ p0) ∧ p7))) ∨ p0 ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3995 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1888 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
  exact (propositional_1628 ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))

abbrev shared_expr_Repair068_7 (c2_kind r2_kind : Int) : Prop := ((¬ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))) ∨ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))
abbrev formula_1889 (c2_kind r2_kind : Int) : Prop := (shared_expr_Repair068_7 c2_kind r2_kind)

theorem propositional_1629 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3996 (c2_kind r2_kind : Int) : (formula_1889 c2_kind r2_kind) := by
  exact (propositional_1629 ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_3997 (r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i239 : ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) : (¬ (formula_301 r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign)) := by
  exact (Or.elim (replay_267 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23) (fun l0 => (False.elim (l0 i239))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3998 (r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i239 : ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) := by
  exact (Or.elim (replay_268 r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim ((replay_3997 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i239) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_3999 (c2_kind r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i239 : ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) (i240 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) : (¬ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))) := by
  exact (Or.elim (replay_3996 c2_kind r2_kind) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3998 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i239)))) (fun t1 => (False.elim (t1 i240))))))

abbrev shared_expr_Repair068_8 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (formula_195 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (formula_179 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign))
abbrev formula_1890 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair068_8 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)

theorem propositional_1630 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((p4 ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p12) ∨ (¬ p13) ∨ (¬ ((p4 ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p8) ∨ (¬ p9)))))))) ∨ (¬ ((¬ p15) ∨ (¬ p16) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p18) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p19) ∨ (¬ p20) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p21) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p22) ∨ (¬ p23) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p24) ∨ (¬ p25) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p21) ∨ (¬ p10) ∨ (¬ p11)))))))))))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4000 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1890 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
  exact (propositional_1630 ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) (formula_179 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (c2_mode ≤ (0 : Int)) (c2_mode ≥ (0 : Int)) ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) (c2_mode ≤ (1 : Int)) (c2_mode ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) (c2_mode ≤ (2 : Int)) (c2_mode ≥ (2 : Int)) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) ((r2_node % (2 : Int)) ≤ (0 : Int)) (c2_mode ≤ (3 : Int)) (c2_mode ≥ (3 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)) (c2_mode ≤ (4 : Int)) (c2_mode ≥ (4 : Int)) (c2_mode ≤ (5 : Int)) (c2_mode ≥ (5 : Int)))

-- Checked replay of unit-resolution.
theorem replay_4001 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i239 : ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) : (formula_195 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_213 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i15) (fun l0 => (False.elim (l0 i239))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_4002 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i239 : ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) (i4 : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) : (formula_179 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_4000 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_4001 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i15 i239)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i4))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_4003 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i239 : ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) (i240 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i4 : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) (i241 : (¬ (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))) : False := by
  exact (Or.elim (replay_3995 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_4002 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i15 i239 i4)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3999 c2_kind r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i239 i240) l1))) (fun t1 => (False.elim (i241 t1))))))

abbrev shared_expr_Repair068_9 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) ∨ (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))))
abbrev formula_1891 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair068_9 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_4004 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) : (formula_1891 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_4003 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i15 (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr q))))) (fun q => nc (Or.inr (Or.inl q))))

theorem propositional_1631 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ p6))) ∨ (¬ p7))) ∨ (¬ (p8 ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ ((¬ p11) ∨ (¬ p12))) ∨ (¬ p6)))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4005 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((formula_177 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) := by
  exact (propositional_1631 ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))) ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)))

abbrev shared_expr_Repair068_10 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)))) ∨ (¬ (formula_177 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)))
abbrev formula_1892 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair068_10 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)

theorem propositional_1632 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4006 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1892 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
  exact (propositional_1632 ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign))) (formula_177 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))

abbrev shared_expr_Repair068_11 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign))) ∨ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))
abbrev formula_1893 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair068_11 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)

theorem propositional_1633 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ (¬ ((¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p6))) ∨ (¬ (p7 ∨ p13 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17)))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4007 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1893 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
  exact (propositional_1633 ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_4008 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) : ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
  exact (Or.elim (replay_4007 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim (i242 t0))))

-- Checked replay of unit-resolution.
theorem replay_4009 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) (i243 : (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)) : (¬ (formula_177 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) := by
  exact (Or.elim (replay_4006 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim (l0 i243))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_4008 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign i242)))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_4010 (c2_depth r2_depth : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_4011 (c2_depth r2_depth : Int) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) := by
  exact (Or.elim (replay_4010 c2_depth r2_depth) (fun l0 => (False.elim (i242 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_4012 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) (i243 : (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)) : False := by
  exact (Or.elim (replay_4005 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (fun l0 => (False.elim ((replay_4009 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign i242 i243) l0))) (fun t0 => (False.elim ((replay_4011 c2_depth r2_depth i242) t0))))

-- Checked replay of lemma.
theorem replay_4013 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ∨ (¬ (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_4012 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

-- Checked replay of unit-resolution.
theorem replay_4014 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) : (¬ (formula_178 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)) := by
  exact (Or.elim (replay_4013 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim (i242 l0))) (fun t0 => t0))

theorem propositional_1634 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 : Prop) : (((¬ p0) ∨ (¬ ((((¬ p1) ∨ (¬ p2)) ∧ ((((¬ p3) ∨ (¬ p4)) ∧ ((¬ p5) ∨ (¬ p6) ∨ ((((¬ p7) ∨ (¬ p8)) ∧ (¬ p7)) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ (¬ ((¬ p9) ∨ (¬ p10))))))) ∨ ((¬ ((¬ p3) ∨ (¬ p4))) ∧ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p12)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14)))))))) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p13) ∨ (¬ p14) ∨ (¬ p9) ∨ (¬ p10))))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4015 (c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))) ∨ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) := by
  exact (propositional_1634 ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (-1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))

abbrev shared_expr_Repair068_12 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := ((¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)) ∨ (¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) ∨ (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))))
abbrev formula_1894 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair068_12 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem propositional_1635 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4016 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1894 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  exact (propositional_1635 ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)))

abbrev shared_expr_Repair068_13 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))) ∨ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))
abbrev formula_1895 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : Prop := (shared_expr_Repair068_13 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)

theorem propositional_1636 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p2 : p2 <;> simp [case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4017 (c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign : Int) : (formula_1895 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  exact (propositional_1636 (c2_kind ≤ (0 : Int)) (c2_kind ≥ (0 : Int)) (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign))

-- Checked replay of unit-resolution.
theorem replay_4018 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : (¬ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign)))) := by
  exact (Or.elim (replay_2230 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157) (fun l0 => (False.elim (l0 i244))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_4019 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : (formula_796 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) := by
  exact (Or.elim (replay_4017 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (fun l0 => (False.elim ((replay_4018 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i244) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_4020 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : (¬ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_795 c0_depth c0_node c0_sign c2_depth c2_node c2_sign)))) := by
  exact (Or.elim (replay_4016 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (fun l0 => (False.elim (l0 (replay_4019 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i244)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i245))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_4021 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) := by
  exact (Or.elim (replay_4015 c0_depth c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (fun l0 => (False.elim ((replay_4020 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i245 i244) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_4022 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_2231 c0_depth c0_kind c0_node c0_sign c2_depth c2_kind c2_node c2_sign) (fun l0 => (False.elim ((replay_4018 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i244) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_4023 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) := by
  exact (Or.elim (replay_4004 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i15) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_4014 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign i242) l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_4021 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i245 i244)))) (fun t2 => (False.elim (t2 (replay_4022 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i244)))))))))

-- Checked replay of unit-resolution.
theorem replay_4024 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) : (formula_210 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) := by
  exact (Or.elim (replay_3994 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i15) (fun l0 => (False.elim ((replay_4023 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i157 i15 i245 i244 i242) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_4025 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) (i242 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) : (formula_208 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := by
  exact (Or.elim (replay_3992 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (False.elim (l0 (replay_4024 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i157 i15 i245 i244 i242)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_4022 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i244)))) (fun t1 => (Or.elim t1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))))))

theorem propositional_1637 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4026 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_197 c2_depth c2_kind c2_sign r2_group r2_level))) ∨ (formula_197 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (propositional_1637 (r2_mode ≤ (0 : Int)) (r2_mode ≥ (0 : Int)) (formula_197 c2_depth c2_kind c2_sign r2_group r2_level))

theorem propositional_1638 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6))))) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ p0) ∧ (¬ p9)))) ∨ p0 ∨ (¬ p9)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4027 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : ((¬ (formula_197 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) := by
  exact (propositional_1638 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_4028 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : (¬ (formula_197 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_4027 c2_depth c2_kind c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i232 l1))) (fun t1 => (False.elim (t1 (replay_4021 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i245 i244)))))))

-- Checked replay of unit-resolution.
theorem replay_4029 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_197 c2_depth c2_kind c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_4026 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_4028 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level i157 i232 i245 i244) t0))))

theorem propositional_1639 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4030 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_199 c2_depth c2_kind c2_sign r2_group r2_level))) ∨ (formula_199 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (propositional_1639 (r2_mode ≤ (1 : Int)) (r2_mode ≥ (1 : Int)) (formula_199 c2_depth c2_kind c2_sign r2_group r2_level))

theorem propositional_1640 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6))))) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ p0) ∧ (¬ p9)))) ∨ p0 ∨ (¬ p9)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4031 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : ((¬ (formula_199 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) := by
  exact (propositional_1640 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_4032 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : (¬ (formula_199 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_4031 c2_depth c2_kind c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i232 l1))) (fun t1 => (False.elim (t1 (replay_4021 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign i157 i245 i244)))))))

-- Checked replay of unit-resolution.
theorem replay_4033 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level r2_mode : Int) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i232 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i245 : ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) (i244 : ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) : ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_199 c2_depth c2_kind c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_4030 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_4032 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign r2_group r2_level i157 i232 i245 i244) t0))))

abbrev shared_expr_Repair068_14 (c1_depth c1_kind c1_node c1_sign r2_level : Int) : Prop := ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) ∨ (¬ ((c1_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))
abbrev formula_1896 (c1_depth c1_kind c1_node c1_sign r2_level : Int) : Prop := (shared_expr_Repair068_14 c1_depth c1_kind c1_node c1_sign r2_level)

abbrev shared_expr_Repair068_15 (c1_depth c1_kind c1_node c1_sign r2_level : Int) : Prop := ((¬ (formula_1896 c1_depth c1_kind c1_node c1_sign r2_level)) ∨ (¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) ∨ (¬ ((c1_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))
abbrev formula_1897 (c1_depth c1_kind c1_node c1_sign r2_level : Int) : Prop := (shared_expr_Repair068_15 c1_depth c1_kind c1_node c1_sign r2_level)

theorem propositional_1641 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4034 (c1_depth c1_kind c1_node c1_sign r2_level : Int) : (formula_1897 c1_depth c1_kind c1_node c1_sign r2_level) := by
  exact (propositional_1641 (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)) ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))) ((c1_node % (2 : Int)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))

theorem propositional_1642 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p8) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4035 (c1_depth c1_kind c1_node c1_sign r0_level : Int) : ((formula_354 c1_depth c1_kind c1_node c1_sign r0_level) ∨ ((c1_node % (2 : Int)) ≤ (0 : Int))) := by
  exact (propositional_1642 (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)) (c1_sign ≤ (2 : Int)) (c1_sign ≥ (2 : Int)) ((r0_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ((r0_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c1_node % (2 : Int)) ≤ (0 : Int)))

theorem propositional_1643 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4036 (c1_depth c1_kind c1_node c1_sign r0_group r0_level : Int) : ((¬ (formula_355 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) ∨ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))) ∨ (¬ (formula_354 c1_depth c1_kind c1_node c1_sign r0_level))) := by
  exact (propositional_1643 ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int)))) (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)) ((r0_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ((r0_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))) (formula_354 c1_depth c1_kind c1_node c1_sign r0_level))

theorem propositional_1644 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_4037 (c1_depth c1_kind c1_node c1_sign r0_group r0_level r0_mode : Int) : (((¬ (r0_mode ≤ (4 : Int))) ∨ (¬ (r0_mode ≥ (4 : Int))) ∨ (¬ (formula_355 c1_depth c1_kind c1_node c1_sign r0_group r0_level))) ∨ (formula_355 c1_depth c1_kind c1_node c1_sign r0_group r0_level)) := by
  exact (propositional_1644 (r0_mode ≤ (4 : Int)) (r0_mode ≥ (4 : Int)) (formula_355 c1_depth c1_kind c1_node c1_sign r0_group r0_level))

end H4Formal.Generated.Repair
