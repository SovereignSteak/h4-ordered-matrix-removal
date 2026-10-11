import H4Formal.Certificates.CheckedClassification.Classification062

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of unit-resolution.
theorem replay_3566 (c2_depth c2_node c2_sign r1_depth r2_depth r2_node r2_sign : Int) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_3563 c2_depth r1_depth r2_depth) (fun l0 => (False.elim (l0 (replay_3565 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i217)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i219))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3567 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ ((¬ (formula_1823 c2_node c2_sign r1_node r1_sign)) ∨ (¬ (formula_1824 c2_node c2_sign r1_node r1_sign)))) := by
  exact (Or.elim (replay_3556 c2_depth c2_node c2_sign r1_depth r1_node r1_sign) (fun l0 => (False.elim (l0 i220))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3566 c2_depth c2_node c2_sign r1_depth r2_depth r2_node r2_sign i219 i217)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3562 c2_depth c2_node c2_sign r1_depth r2_depth r2_node r2_sign i218 i217)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_3568 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (formula_1823 c2_node c2_sign r1_node r1_sign) := by
  exact (Or.elim (replay_3555 c2_node c2_sign r1_node r1_sign) (fun l0 => (False.elim ((replay_3567 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i219 i218 i220 i217) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))))

theorem propositional_1599 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3569 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1164 c2_node c2_sign r2_node r2_sign) ∨ (c2_sign ≥ (0 : Int))) := by
  exact (propositional_1599 (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Classification063_0 (c2_node c2_sign r2_node r2_sign : Int) : Prop := ((¬ ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)))) ∨ (¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)))
abbrev formula_1953 (c2_node c2_sign r2_node r2_sign : Int) : Prop := (shared_expr_Classification063_0 c2_node c2_sign r2_node r2_sign)

theorem propositional_1600 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3570 (c2_node c2_sign r2_node r2_sign : Int) : (formula_1953 c2_node c2_sign r2_node r2_sign) := by
  exact (propositional_1600 (formula_1164 c2_node c2_sign r2_node r2_sign) (formula_1165 c2_node c2_sign r2_node r2_sign))

theorem propositional_1601 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3571 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) : ((formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ∨ ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)))) := by
  exact (propositional_1601 ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign))))

-- Checked replay of unit-resolution.
theorem replay_3572 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign))) := by
  exact (Or.elim (replay_3571 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (fun l0 => (False.elim (i217 l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

theorem propositional_1602 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3573 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1165 c2_node c2_sign r2_node r2_sign) ∨ (c2_sign ≥ (1 : Int))) := by
  exact (propositional_1602 ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_3574 (c2_sign : Int) : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3575 (c2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) : (¬ (c2_sign ≥ (1 : Int))) := by
  exact (Or.elim (replay_3574 c2_sign) (fun l0 => (False.elim (l0 i211))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3576 (c2_node c2_sign r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) : (formula_1165 c2_node c2_sign r2_node r2_sign) := by
  exact (Or.elim (replay_3573 c2_node c2_sign r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim ((replay_3575 c2_sign i211) t0))))

-- Checked replay of unit-resolution.
theorem replay_3577 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) := by
  exact (Or.elim (replay_3570 c2_node c2_sign r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_3572 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i217)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_3576 c2_node c2_sign r2_node r2_sign i211)))))))

-- Checked replay of unit-resolution.
theorem replay_3578 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (c2_sign ≥ (0 : Int)) := by
  exact (Or.elim (replay_3569 c2_node c2_sign r2_node r2_sign) (fun l0 => (False.elim ((replay_3577 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i211 i217) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3579 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))) := by
  exact (Or.elim (replay_3554 c2_node c2_sign r1_node r1_sign) (fun l0 => (False.elim (l0 (replay_3568 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i219 i218 i220 i217)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i211))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3578 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i211 i217)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i209))) (fun t3 => t3))))))))

-- Checked replay of th-lemma.
theorem replay_3580 (r2_node : Int) : ((¬ (r2_node = (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ∨ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_3581 (r2_node : Int) : (False ∨ (r2_node = (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of true-axiom.
theorem replay_3582  : True := by
  exact True.intro

-- Checked replay of unit-resolution.
theorem replay_3583 (r2_node : Int) : (r2_node = (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int)))) := by
  exact (Or.elim (replay_3581 r2_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3584 (r2_node : Int) : ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3580 r2_node) (fun l0 => (False.elim (l0 (replay_3583 r2_node)))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_3585 (r2_node : Int) : (False ∨ ((r2_node % (2 : Int)) ≤ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3586 (r2_node : Int) : ((r2_node % (2 : Int)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_3585 r2_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_3587 (r1_node : Int) : ((¬ (r1_node = (((2 : Int) * (r1_node / (2 : Int))) + (r1_node % (2 : Int))))) ∨ ((r1_node + ((-1 : Int) * (((2 : Int) * (r1_node / (2 : Int))) + (r1_node % (2 : Int))))) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_3588 (r1_node : Int) : (False ∨ (r1_node = (((2 : Int) * (r1_node / (2 : Int))) + (r1_node % (2 : Int))))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3589 (r1_node : Int) : (r1_node = (((2 : Int) * (r1_node / (2 : Int))) + (r1_node % (2 : Int)))) := by
  exact (Or.elim (replay_3588 r1_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3590 (r1_node : Int) : ((r1_node + ((-1 : Int) * (((2 : Int) * (r1_node / (2 : Int))) + (r1_node % (2 : Int))))) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3587 r1_node) (fun l0 => (False.elim (l0 (replay_3589 r1_node)))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_3591 (r1_node : Int) : (False ∨ ((r1_node % (2 : Int)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3592 (r1_node : Int) : ((r1_node % (2 : Int)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3591 r1_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

theorem propositional_1603 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3593 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1164 c2_node c2_sign r2_node r2_sign) ∨ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) := by
  exact (propositional_1603 (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3594 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3593 c2_node c2_sign r2_node r2_sign) (fun l0 => (False.elim ((replay_3577 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i211 i217) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3595 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_3553 c2_node r1_node r2_node) (fun l0 => (False.elim (l0 (replay_3592 r1_node)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3579 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i211 i219 i218 i209 i220 i217) l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3586 r2_node)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3594 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i211 i217)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_3584 r2_node)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_3590 r1_node)))) (fun t5 => t5))))))))))))

-- Checked replay of unit-resolution.
theorem replay_3596 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) := by
  exact (Or.elim (replay_3552 r1_node r2_node) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3595 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i211 i219 i218 i209 i220 i217) t0))))

abbrev shared_expr_Classification063_1 (c2_node r1_node r2_node : Int) : Prop := ((¬ ((r1_node % (2 : Int)) ≥ (0 : Int))) ∨ ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ∨ (¬ ((r2_node % (2 : Int)) ≤ (1 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * (((2 : Int) * (r1_node / (2 : Int))) + (r1_node % (2 : Int))))) ≥ (0 : Int))) ∨ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))
abbrev formula_1954 (c2_node r1_node r2_node : Int) : Prop := (shared_expr_Classification063_1 c2_node r1_node r2_node)

-- Checked replay of th-lemma.
theorem replay_3597 (c2_node r1_node r2_node : Int) : (formula_1954 c2_node r1_node r2_node) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3598 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3597 c2_node r1_node r2_node) (fun l0 => (False.elim (l0 (replay_3592 r1_node)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3579 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i211 i219 i218 i209 i220 i217) l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3586 r2_node)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3594 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i211 i217)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_3584 r2_node)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_3590 r1_node)))) (fun t5 => t5))))))))))))

-- Checked replay of unit-resolution.
theorem replay_3599 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i211 : (c2_sign ≤ (0 : Int))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i221 : (formula_23 r1_node r1_sign r2_node r2_sign)) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : False := by
  exact (Or.elim (replay_3525 r1_node r1_sign r2_node r2_sign) (fun l0 => (False.elim (l0 i221))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3596 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i211 i219 i218 i209 i220 i217)))) (fun t1 => (False.elim (t1 (replay_3598 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i211 i219 i218 i209 i220 i217)))))))

abbrev shared_expr_Classification063_2 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ∨ (¬ (formula_23 r1_node r1_sign r2_node r2_sign)) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
abbrev formula_1955 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification063_2 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_3600 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_1955 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3599 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (fun q => nc (Or.inl q)))

theorem propositional_1604 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ (p6 ∨ p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11)))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3601 (c2_node c2_sign h r1_depth r1_node r1_sign : Int) : ((formula_1822 c2_node c2_sign h r1_depth r1_node r1_sign) ∨ (formula_1820 c2_node c2_sign h r1_depth r1_node r1_sign)) := by
  exact (propositional_1604 (formula_1820 c2_node c2_sign h r1_depth r1_node r1_sign) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

abbrev shared_expr_Classification063_3 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1822 c2_node c2_sign h r1_depth r1_node r1_sign)))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1822 c2_node c2_sign h r1_depth r1_node r1_sign)))
abbrev formula_1956 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification063_3 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign)

theorem propositional_1605 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3602 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign : Int) : (formula_1956 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_1605 ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) (formula_1822 c2_node c2_sign h r1_depth r1_node r1_sign))

-- Checked replay of th-lemma.
theorem replay_3603 (c2_depth r1_depth r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification063_4 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign))) ∨ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))
abbrev formula_1957 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification063_4 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign)

theorem propositional_1606 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8))) ∨ (¬ ((¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p8))) ∨ (¬ (p2 ∨ p13 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17)))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3604 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) : (formula_1957 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) := by
  exact (propositional_1606 ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

theorem propositional_1607 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ p4))) ∨ (¬ p5))) ∨ (¬ p6)) ∨ p6) := by
  classical
  first | (by_cases case_p6 : p6 <;> simp [case_p6, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3605 (c2_node c2_sign r1_node r1_sign : Int) : (((¬ (formula_1823 c2_node c2_sign r1_node r1_sign)) ∨ (¬ (formula_1824 c2_node c2_sign r1_node r1_sign))) ∨ (formula_1824 c2_node c2_sign r1_node r1_sign)) := by
  exact (propositional_1607 (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) (formula_1824 c2_node c2_sign r1_node r1_sign))

abbrev shared_expr_Classification063_5 (c2_node c2_sign r1_node r1_sign : Int) : Prop := ((¬ (formula_1824 c2_node c2_sign r1_node r1_sign)) ∨ ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))))
abbrev formula_1958 (c2_node c2_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification063_5 c2_node c2_sign r1_node r1_sign)

theorem propositional_1608 (p0 p1 p2 p3 : Prop) : ((¬ (p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3))) ∨ p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> by_cases case_p2 : p2 <;> simp [case_p0, case_p1, case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3606 (c2_node c2_sign r1_node r1_sign : Int) : (formula_1958 c2_node c2_sign r1_node r1_sign) := by
  exact (propositional_1608 ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))

abbrev shared_expr_Classification063_6 (c2_node r1_node r2_node : Int) : Prop := ((¬ ((r2_node % (2 : Int)) ≤ (1 : Int))) ∨ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)) ∨ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ ((r1_node + ((-1 : Int) * (((2 : Int) * (r1_node / (2 : Int))) + (r1_node % (2 : Int))))) ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≤ (0 : Int))) ∨ (¬ ((r1_node % (2 : Int)) ≥ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_1959 (c2_node r1_node r2_node : Int) : Prop := (shared_expr_Classification063_6 c2_node r1_node r2_node)

-- Checked replay of th-lemma.
theorem replay_3607 (c2_node r1_node r2_node : Int) : (formula_1959 c2_node r1_node r2_node) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1609 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3608 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1165 c2_node c2_sign r2_node r2_sign) ∨ (¬ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)))) := by
  exact (propositional_1609 ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3609 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)) := by
  exact (Or.elim (replay_3570 c2_node c2_sign r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_3572 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i217)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i222))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3610 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) := by
  exact (Or.elim (replay_3608 c2_node c2_sign r2_node r2_sign) (fun l0 => (False.elim ((replay_3609 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i222 i217) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3611 (c2_depth c2_node c2_sign r1_node r2_depth r2_node r2_sign : Int) (i223 : (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) := by
  exact (Or.elim (replay_3607 c2_node r1_node r2_node) (fun l0 => (False.elim (l0 (replay_3586 r2_node)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i223 l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim ((replay_3610 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i222 i217) l2))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3590 r1_node)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_3584 r2_node)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_3592 r1_node)))) (fun t5 => t5))))))))))))

theorem propositional_1610 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6)))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3612 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1165 c2_node c2_sign r2_node r2_sign) ∨ (c2_sign ≤ (1 : Int))) := by
  exact (propositional_1610 ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3613 (c2_depth c2_node c2_sign r2_depth r2_node r2_sign : Int) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (c2_sign ≤ (1 : Int)) := by
  exact (Or.elim (replay_3612 c2_node c2_sign r2_node r2_sign) (fun l0 => (False.elim ((replay_3609 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i222 i217) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3614 (c2_depth c2_node c2_sign r1_node r1_sign r2_depth r2_node r2_sign : Int) (i223 : (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) (i224 : (c2_sign ≥ (1 : Int))) (i225 : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : (¬ (formula_1824 c2_node c2_sign r1_node r1_sign)) := by
  exact (Or.elim (replay_3606 c2_node c2_sign r1_node r1_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3611 c2_depth c2_node c2_sign r1_node r2_depth r2_node r2_sign i223 i222 i217) l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3613 c2_depth c2_node c2_sign r2_depth r2_node r2_sign i222 i217)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i224))) (fun t3 => (False.elim (t3 i225))))))))))

-- Checked replay of unit-resolution.
theorem replay_3615 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i223 : (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) (i224 : (c2_sign ≥ (1 : Int))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i225 : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) (i217 : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign))) : False := by
  exact (Or.elim (replay_3605 c2_node c2_sign r1_node r1_sign) (fun l0 => (False.elim ((replay_3567 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i219 i218 i220 i217) l0))) (fun t0 => (False.elim ((replay_3614 c2_depth c2_node c2_sign r1_node r1_sign r2_depth r2_node r2_sign i223 i224 i225 i222 i217) t0))))

abbrev shared_expr_Classification063_7 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) ∨ (¬ (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) ∨ (¬ (c2_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∨ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)) ∨ (¬ (formula_1164 c2_node c2_sign r2_node r2_sign)))
abbrev formula_1960 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification063_7 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_3616 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_1960 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3615 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))) (fun q => nc (Or.inl q)))

-- Checked replay of th-lemma.
theorem replay_3617 (c2_sign : Int) : ((c2_sign ≤ (0 : Int)) ∨ (c2_sign ≥ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3618 (c2_sign : Int) (i226 : (¬ (c2_sign ≤ (0 : Int)))) : (c2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_3617 c2_sign) (fun l0 => (False.elim (i226 l0))) (fun t0 => t0))

theorem propositional_1611 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3619 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ (r2_sign ≥ (1 : Int))) := by
  exact (propositional_1611 ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3620 (h r2_depth : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) : ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) := by
  exact (Or.elim (replay_219 h r2_depth) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i227 t0))))

-- Checked replay of unit-resolution.
theorem replay_3621 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) := by
  exact (Or.elim (replay_218 h r2_depth r2_sign) (fun l0 => (False.elim (l0 i228))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3620 h r2_depth i227)))) (fun t1 => (Or.elim t1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))))

-- Checked replay of unit-resolution.
theorem replay_3622 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) : (¬ (r2_sign ≥ (2 : Int))) := by
  exact (Or.elim (replay_217 r2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3621 h r2_depth r2_sign i227 i228)))))

-- Checked replay of unit-resolution.
theorem replay_3623 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) : ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))) := by
  exact (Or.elim (replay_205 r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3622 h r2_depth r2_sign i227 i228) t0))))

-- Checked replay of unit-resolution.
theorem replay_3624 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) := by
  exact (Or.elim (replay_384 r2_sign) (fun l0 => (False.elim (l0 i130))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_3623 h r2_depth r2_sign i227 i228)))))))

-- Checked replay of unit-resolution.
theorem replay_3625 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (r2_sign ≤ (0 : Int)) := by
  exact (Or.elim (replay_207 r2_sign) (fun l0 => (False.elim ((replay_3624 h r2_depth r2_sign i227 i228 i130) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3626 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (¬ (r2_sign ≥ (1 : Int))) := by
  exact (Or.elim (replay_202 r2_sign) (fun l0 => (False.elim (l0 (replay_3625 h r2_depth r2_sign i227 i228 i130)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3627 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (formula_1162 c2_node c2_sign h r2_depth r2_node r2_sign) := by
  exact (Or.elim (replay_3619 c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim ((replay_3626 h r2_depth r2_sign i227 i228 i130) t0))))

theorem propositional_1612 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3628 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
  exact (propositional_1612 ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3629 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) : (formula_1161 c2_node c2_sign h r2_depth r2_node r2_sign) := by
  exact (Or.elim (replay_3628 c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t105))))))))))))))))))) (fun t0 => (False.elim (i227 t0))))

-- Checked replay of unit-resolution.
theorem replay_3630 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i229 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) : (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
  exact (Or.elim (replay_3549 c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3629 c2_node c2_sign h r2_depth r2_node r2_sign i227)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i229))) (fun t2 => (False.elim (t2 (replay_3627 c2_node c2_sign h r2_depth r2_node r2_sign i227 i228 i130)))))))))

-- Checked replay of unit-resolution.
theorem replay_3631 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i229 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) : ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign))) := by
  exact (Or.elim (replay_3550 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_3630 c2_node c2_sign h r2_depth r2_node r2_sign i227 i228 i130 i229) t0))))

-- Checked replay of unit-resolution.
theorem replay_3632 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i229 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign)) := by
  exact (Or.elim (replay_3551 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i230))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i14))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i231))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3631 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign i227 i228 i130 i229)))) (fun t3 => t3))))))))

theorem propositional_1613 (p0 p1 p2 p3 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3633 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1165 c2_node c2_sign r2_node r2_sign) ∨ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) := by
  exact (propositional_1613 ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))))

-- Checked replay of unit-resolution.
theorem replay_3634 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))) := by
  exact (Or.elim (replay_203 r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3626 h r2_depth r2_sign i227 i228 i130) t0))))

-- Checked replay of unit-resolution.
theorem replay_3635 (h r2_depth r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) := by
  exact (Or.elim (replay_204 r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3634 h r2_depth r2_sign i227 i228 i130)))) (fun t1 => (False.elim (t1 (replay_3623 h r2_depth r2_sign i227 i228)))))))

-- Checked replay of unit-resolution.
theorem replay_3636 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (formula_1165 c2_node c2_sign r2_node r2_sign) := by
  exact (Or.elim (replay_3633 c2_node c2_sign r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim ((replay_3635 h r2_depth r2_sign i227 i228 i130) t0))))

-- Checked replay of unit-resolution.
theorem replay_3637 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i228 : (formula_61 h r2_depth r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) : (¬ ((¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ (formula_1165 c2_node c2_sign r2_node r2_sign)))) := by
  exact (Or.elim (replay_3570 c2_node c2_sign r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i222))) (fun t1 => (False.elim (t1 (replay_3636 c2_node c2_sign h r2_depth r2_node r2_sign i227 i228 i130)))))))

-- Checked replay of unit-resolution.
theorem replay_3638 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i227 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i229 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) (i222 : (formula_1164 c2_node c2_sign r2_node r2_sign)) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : False := by
  exact (Or.elim (replay_3571 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) (fun l0 => (False.elim ((replay_3632 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i227 i14 i228 i231 i130 i229 i230) l0))) (fun t0 => (False.elim ((replay_3637 c2_node c2_sign h r2_depth r2_node r2_sign i227 i228 i130 i222) t0))))

abbrev shared_expr_Classification063_8 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∨ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∨ (¬ (formula_1164 c2_node c2_sign r2_node r2_sign)) ∨ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ (formula_61 h r2_depth r2_sign)))
abbrev formula_1961 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Classification063_8 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_3639 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_1961 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3638 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))))

theorem propositional_1614 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3640 (c2_node c2_sign r2_node r2_sign : Int) : ((formula_1164 c2_node c2_sign r2_node r2_sign) ∨ (c2_sign ≤ (0 : Int))) := by
  exact (propositional_1614 (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((c2_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3641 (c2_node c2_sign r2_node r2_sign : Int) (i226 : (¬ (c2_sign ≤ (0 : Int)))) : (formula_1164 c2_node c2_sign r2_node r2_sign) := by
  exact (Or.elim (replay_3640 c2_node c2_sign r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim (i226 t0))))

theorem propositional_1615 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3642 (c2_node c2_sign r2_node r2_sign : Int) : (((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∨ (c2_sign ≤ (0 : Int))) := by
  exact (propositional_1615 (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3643 (c2_node c2_sign r2_node r2_sign : Int) (i226 : (¬ (c2_sign ≤ (0 : Int)))) : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) := by
  exact (Or.elim (replay_3642 c2_node c2_sign r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim (i226 t0))))

-- Checked replay of unit-resolution.
theorem replay_3644 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3639 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i14))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i230))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i231))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_3641 c2_node c2_sign r2_node r2_sign i226)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_3643 c2_node c2_sign r2_node r2_sign i226)))) (fun t5 => (Or.elim t5 (fun l6 => (False.elim (l6 i130))) (fun t6 => (False.elim (t6 i228))))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_3645 (c2_depth c2_kind c2_node c2_sign h r1_depth r2_depth r2_kind r2_node r2_sign : Int) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_220 h r1_depth r2_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i218 l1))) (fun t1 => (False.elim (t1 (replay_3644 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i14 i228 i231 i226 i130 i230)))))))

-- Checked replay of unit-resolution.
theorem replay_3646 (c2_depth c2_kind c2_node c2_sign h r1_depth r2_depth r2_kind r2_node r2_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_221 h r1_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3645 c2_depth c2_kind c2_node c2_sign h r1_depth r2_depth r2_kind r2_node r2_sign i14 i228 i231 i226 i218 i130 i230)))) (fun t1 => (False.elim (t1 i232))))))

-- Checked replay of unit-resolution.
theorem replay_3647 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i233 : (formula_6 h r1_depth r1_sign)) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_222 h r1_depth r1_sign) (fun l0 => (False.elim (l0 i233))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3646 c2_depth c2_kind c2_node c2_sign h r1_depth r2_depth r2_kind r2_node r2_sign i232 i14 i228 i231 i226 i218 i130 i230) l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3648 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i233 : (formula_6 h r1_depth r1_sign)) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) := by
  exact (Or.elim (replay_223 r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3647 c2_depth c2_kind c2_node c2_sign h r1_depth r1_sign r2_depth r2_kind r2_node r2_sign i232 i233 i14 i228 i231 i226 i218 i130 i230) t0))))

theorem propositional_1616 (p0 p1 p2 p3 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3649 (r1_sign r2_sign : Int) : (((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) ∨ (r2_sign ≤ (0 : Int))) := by
  exact (propositional_1616 (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3650 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_1768 h r2_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3644 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i14 i228 i231 i226 i130 i230)))) (fun t1 => (False.elim (t1 i234))))))

-- Checked replay of unit-resolution.
theorem replay_3651 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_1767 h r2_depth r2_sign) (fun l0 => (False.elim (l0 i228))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3650 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i130 i230) l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3652 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (r2_sign ≥ (2 : Int)) := by
  exact (Or.elim (replay_205 r2_sign) (fun l0 => (False.elim ((replay_3651 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i130 i230) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3653 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (r2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_208 r2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3652 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i130 i230)))))

-- Checked replay of unit-resolution.
theorem replay_3654 (c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ (r2_sign ≤ (0 : Int))) := by
  exact (Or.elim (replay_202 r2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3653 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i130 i230)))))

-- Checked replay of unit-resolution.
theorem replay_3655 (c2_depth c2_kind c2_node c2_sign h r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) := by
  exact (Or.elim (replay_3649 r1_sign r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim ((replay_3654 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i130 i230) t0))))

-- Checked replay of unit-resolution.
theorem replay_3656 (c2_depth c2_kind c2_node c2_sign h r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i221 : (formula_23 r1_node r1_sign r2_node r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) := by
  exact (Or.elim (replay_3524 r1_node r1_sign r2_node r2_sign) (fun l0 => (False.elim (l0 i221))) (fun t0 => (Or.elim t0 (fun l1 => (Or.elim l1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t1 => (False.elim (t1 (replay_3655 c2_depth c2_kind c2_node c2_sign h r1_sign r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i130 i230)))))))

-- Checked replay of unit-resolution.
theorem replay_3657 (c2_depth c2_kind c2_node c2_sign h r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i221 : (formula_23 r1_node r1_sign r2_node r2_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_3525 r1_node r1_sign r2_node r2_sign) (fun l0 => (False.elim (l0 i221))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3656 c2_depth c2_kind c2_node c2_sign h r1_node r1_sign r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i221 i130 i230)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3658 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i233 : (formula_6 h r1_depth r1_sign)) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i221 : (formula_23 r1_node r1_sign r2_node r2_sign)) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (formula_1166 c2_depth c2_node c2_sign r2_depth r2_node r2_sign) := by
  exact (Or.elim (replay_3616 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i220))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3618 c2_sign i226)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_3648 c2_depth c2_kind c2_node c2_sign h r1_depth r1_sign r2_depth r2_kind r2_node r2_sign i232 i233 i14 i228 i231 i226 i218 i130 i230)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i219))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (i218 l5))) (fun t5 => (Or.elim t5 (fun l6 => (False.elim ((replay_3657 c2_depth c2_kind c2_node c2_sign h r1_node r1_sign r2_depth r2_kind r2_node r2_sign i234 i14 i228 i231 i226 i221 i130 i230) l6))) (fun t6 => (False.elim (t6 (replay_3641 c2_node c2_sign r2_node r2_sign i226)))))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_3659 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i233 : (formula_6 h r1_depth r1_sign)) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i221 : (formula_23 r1_node r1_sign r2_node r2_sign)) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1163 c2_node c2_sign h r2_depth r2_node r2_sign)))) := by
  exact (Or.elim (replay_3551 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i230))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i14))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i231))) (fun t2 => (Or.elim t2 (fun l3 => l3) (fun t3 => (False.elim (t3 (replay_3658 c2_depth c2_kind c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign i232 i234 i233 i14 i228 i231 i226 i219 i221 i218 i220 i130 i230)))))))))))

-- Checked replay of unit-resolution.
theorem replay_3660 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i234 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i233 : (formula_6 h r1_depth r1_sign)) (i14 : ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) (i228 : (formula_61 h r2_depth r2_sign)) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i226 : (¬ (c2_sign ≤ (0 : Int)))) (i219 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i221 : (formula_23 r1_node r1_sign r2_node r2_sign)) (i218 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i130 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i230 : (formula_1167 c2_depth c2_kind c2_node c2_sign h r2_depth r2_kind r2_node r2_sign)) : ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3604 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim ((replay_3659 c2_depth c2_kind c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign i232 i234 i233 i14 i228 i231 i226 i219 i221 i218 i220 i130 i230) l0))) (fun t0 => t0))

end H4Formal.Generated.Classification
