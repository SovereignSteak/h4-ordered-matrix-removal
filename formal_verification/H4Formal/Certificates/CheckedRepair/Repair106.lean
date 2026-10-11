import H4Formal.Certificates.CheckedRepair.Repair105

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of unit-resolution.
theorem replay_7006 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : (¬ (formula_1 c2_node c2_sign h r2_depth r2_node r2_sign)) := by
  exact (Or.elim (replay_1 c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim (l0 i484))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6619 c2_node c2_sign r2_node r2_sign i422)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i424))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_7007 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_7005 c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim ((replay_7006 c2_node c2_sign h r2_depth r2_node r2_sign i422 i424 i484) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7008 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_7004 c2_node r2_node) (fun l0 => l0) (fun t0 => (False.elim ((replay_7007 c2_node c2_sign h r2_depth r2_node r2_sign i422 i424 i484) t0))))

abbrev shared_expr_Repair106_0 (c2_node c2_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (formula_1015 c2_node c2_sign h r1_depth r1_node r1_sign)) ∨ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∨ ((r1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ∨ (¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))
abbrev formula_2677 (c2_node c2_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair106_0 c2_node c2_sign h r1_depth r1_node r1_sign)

theorem propositional_2321 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ (p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7009 (c2_node c2_sign h r1_depth r1_node r1_sign : Int) : (formula_2677 c2_node c2_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2321 ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_7010 (c2_sign : Int) : ((c2_sign ≤ (0 : Int)) ∨ (c2_sign ≥ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7011 (c2_sign : Int) (i422 : (¬ (c2_sign ≤ (0 : Int)))) : (c2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_7010 c2_sign) (fun l0 => (False.elim (i422 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7012 (c2_node c2_sign h r1_depth r1_node r1_sign : Int) (i486 : (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (i485 : (r1_sign ≥ (1 : Int))) (i487 : (r1_sign ≤ (1 : Int))) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i488 : (c2_sign ≤ (1 : Int))) (i489 : (formula_1015 c2_node c2_sign h r1_depth r1_node r1_sign)) : ((r1_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_7009 c2_node c2_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim (l0 i489))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i486 l1))) (fun t1 => (Or.elim t1 (fun l2 => l2) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i487))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i485))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i488))) (fun t5 => (False.elim (t5 (replay_7011 c2_sign i422)))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_7013 (c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i486 : (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (i485 : (r1_sign ≥ (1 : Int))) (i487 : (r1_sign ≤ (1 : Int))) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i488 : (c2_sign ≤ (1 : Int))) (i489 : (formula_1015 c2_node c2_sign h r1_depth r1_node r1_sign)) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_7003 c2_node r1_node r2_node) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7008 c2_node c2_sign h r2_depth r2_node r2_sign i422 i424 i484)))) (fun t1 => (False.elim (t1 (replay_7012 c2_node c2_sign h r1_depth r1_node r1_sign i486 i485 i487 i422 i488 i489)))))))

-- Checked replay of unit-resolution.
theorem replay_7014 (c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i486 : (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (i485 : (r1_sign ≥ (1 : Int))) (i487 : (r1_sign ≤ (1 : Int))) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i488 : (c2_sign ≤ (1 : Int))) (i490 : (formula_556 r1_node r1_sign r2_node r2_sign)) (i489 : (formula_1015 c2_node c2_sign h r1_depth r1_node r1_sign)) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : (¬ ((¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_534 r1_node r1_sign r2_node r2_sign) (fun l0 => (False.elim (l0 i490))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_7013 c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign i486 i485 i487 i422 i488 i489 i424 i484)))))))

theorem propositional_2322 (p0 p1 p2 p3 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7015 (r1_sign r2_sign : Int) : (((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) ∨ (r2_sign ≤ (0 : Int))) := by
  exact (propositional_2322 (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)))

theorem propositional_2323 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7016 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_1 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ (r2_sign ≥ (1 : Int))) := by
  exact (propositional_2323 ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_7017 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : (r2_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_7016 c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim ((replay_7006 c2_node c2_sign h r2_depth r2_node r2_sign i422 i424 i484) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7018 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : (¬ (r2_sign ≤ (0 : Int))) := by
  exact (Or.elim (replay_739 r2_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_7017 c2_node c2_sign h r2_depth r2_node r2_sign i422 i424 i484)))))

-- Checked replay of unit-resolution.
theorem replay_7019 (c2_node c2_sign h r1_sign r2_depth r2_node r2_sign : Int) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) := by
  exact (Or.elim (replay_7015 r1_sign r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim ((replay_7018 c2_node c2_sign h r2_depth r2_node r2_sign i422 i424 i484) t0))))

-- Checked replay of unit-resolution.
theorem replay_7020 (c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i486 : (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (i485 : (r1_sign ≥ (1 : Int))) (i487 : (r1_sign ≤ (1 : Int))) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i488 : (c2_sign ≤ (1 : Int))) (i490 : (formula_556 r1_node r1_sign r2_node r2_sign)) (i489 : (formula_1015 c2_node c2_sign h r1_depth r1_node r1_sign)) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i484 : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)) : False := by
  exact (Or.elim (replay_3176 r1_node r1_sign r2_node r2_sign) (fun l0 => (False.elim (l0 i490))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_7014 c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign i486 i485 i487 i422 i488 i490 i489 i424 i484) l1))) (fun t1 => (False.elim (t1 (replay_7019 c2_node c2_sign h r1_sign r2_depth r2_node r2_sign i422 i424 i484)))))))

abbrev shared_expr_Repair106_1 (c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((c2_sign ≤ (0 : Int)) ∨ (¬ (formula_556 r1_node r1_sign r2_node r2_sign)) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∨ (¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (formula_1015 c2_node c2_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign)))
abbrev formula_2678 (c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair106_1 c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_7021 (c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_2678 c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_7020 c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))))))

-- Checked replay of unit-resolution.
theorem replay_7022 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i482 : (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign))))) : (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign) := by
  exact (Or.elim (replay_6449 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim (i482 l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))))

-- Checked replay of unit-resolution.
theorem replay_7023 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i486 : (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (i485 : (r1_sign ≥ (1 : Int))) (i487 : (r1_sign ≤ (1 : Int))) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i488 : (c2_sign ≤ (1 : Int))) (i490 : (formula_556 r1_node r1_sign r2_node r2_sign)) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i482 : (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign))))) : (¬ (formula_1015 c2_node c2_sign h r1_depth r1_node r1_sign)) := by
  exact (Or.elim (replay_7021 c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign) (fun l0 => (False.elim (i422 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i490))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i485))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (i486 l3))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i487))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i488))) (fun t5 => (Or.elim t5 (fun l6 => l6) (fun t6 => (Or.elim t6 (fun l7 => (False.elim (l7 i424))) (fun t7 => (False.elim (t7 (replay_7022 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign i482)))))))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_7024 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i486 : (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) (i485 : (r1_sign ≥ (1 : Int))) (i487 : (r1_sign ≤ (1 : Int))) (i422 : (¬ (c2_sign ≤ (0 : Int)))) (i488 : (c2_sign ≤ (1 : Int))) (i38 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i490 : (formula_556 r1_node r1_sign r2_node r2_sign)) (i483 : ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i166 : ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)))) (i424 : (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) (i482 : (¬ ((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign))))) : False := by
  exact (Or.elim (replay_6997 c2_node c2_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim ((replay_7002 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign i38 i483 i166 i482) l0))) (fun t0 => (False.elim ((replay_7023 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign i486 i485 i487 i422 i488 i490 i424 i482) t0))))

abbrev shared_expr_Repair106_2 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2 c2_node c2_sign h r2_depth r2_node r2_sign))) ∨ (¬ ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (c2_sign ≤ (0 : Int)) ∨ (¬ (formula_556 r1_node r1_sign r2_node r2_sign)) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∨ (¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign)) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
abbrev formula_2679 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair106_2 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_7025 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_2679 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_7024 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign r2_depth r2_node r2_sign (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (fun q => nc (Or.inl q)))

abbrev shared_expr_Repair106_3 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign : Int) : Prop := ((formula_1020 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign) ∨ ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign))))
abbrev formula_2680 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair106_3 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign)

theorem propositional_2324 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4) ∨ (¬ ((¬ ((¬ p5) ∨ (¬ p6))) ∨ (¬ p7))) ∨ (¬ p8))) ∨ (¬ (p9 ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ p7)))))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7026 (c2_depth c2_node c2_sign h r1_depth r1_node r1_sign : Int) : (formula_2680 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2324 ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign))) ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)))

abbrev shared_expr_Repair106_4 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((formula_1021 c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) ∨ ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) ∨ (¬ (formula_1020 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign)))
abbrev formula_2681 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair106_4 c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign)

theorem propositional_2325 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ∧ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ ((¬ p0) ∧ p7)) ∨ p0 ∨ (¬ p7)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7027 (c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2681 c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) := by
  exact (propositional_2325 ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (2 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) (formula_1020 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign))

abbrev shared_expr_Repair106_5 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((formula_1022 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) ∨ (¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ (formula_1021 c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign)))
abbrev formula_2682 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair106_5 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign)

theorem propositional_2326 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((p4 ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p12) ∨ (¬ p13) ∨ (¬ ((p4 ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p8) ∨ (¬ p9)))))))) ∨ (¬ ((¬ p15) ∨ (¬ p16) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p18) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p19) ∨ (¬ p20) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p21) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p22) ∨ (¬ p23) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p24) ∨ (¬ p25) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p21) ∨ (¬ p10) ∨ (¬ p11))))))))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7028 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2682 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) := by
  exact (propositional_2326 ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) (formula_1021 c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) (c2_mode ≤ (0 : Int)) (c2_mode ≥ (0 : Int)) ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)) ((r1_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) (c2_mode ≤ (1 : Int)) (c2_mode ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) (c2_mode ≤ (2 : Int)) (c2_mode ≥ (2 : Int)) ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))) ((r1_node % (2 : Int)) ≤ (0 : Int)) (c2_mode ≤ (3 : Int)) (c2_mode ≥ (3 : Int)) ((r1_node % (2 : Int)) ≥ (1 : Int)) (c2_mode ≤ (4 : Int)) (c2_mode ≥ (4 : Int)) (c2_mode ≤ (5 : Int)) (c2_mode ≥ (5 : Int)))

-- Checked replay of unit-resolution.
theorem replay_7029 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) : (c2_kind ≥ (1 : Int)) := by
  exact (Or.elim (replay_10 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h) (fun l0 => (False.elim (i491 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7030 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) : (¬ (c2_kind ≤ (0 : Int))) := by
  exact (Or.elim (replay_2495 c2_kind) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_7029 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i491)))))

-- Checked replay of unit-resolution.
theorem replay_7031 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) : ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_2496 c2_kind) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_7030 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i491) t0))))

-- Checked replay of unit-resolution.
theorem replay_7032 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) (i492 : (¬ (formula_1022 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign))) : (¬ (formula_1021 c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign)) := by
  exact (Or.elim (replay_7028 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim (i492 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7031 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i491)))) (fun t1 => t1))))

abbrev shared_expr_Repair106_6 (c2_kind r1_kind : Int) : Prop := ((¬ ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))) ∨ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))
abbrev formula_2683 (c2_kind r1_kind : Int) : Prop := (shared_expr_Repair106_6 c2_kind r1_kind)

theorem propositional_2327 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7033 (c2_kind r1_kind : Int) : (formula_2683 c2_kind r1_kind) := by
  exact (propositional_2327 ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_7034 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) : (c2_kind ≤ (1 : Int)) := by
  exact (Or.elim (replay_5963 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h) (fun l0 => (False.elim (i491 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7035 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) : (¬ (c2_kind ≥ (2 : Int))) := by
  exact (Or.elim (replay_24 c2_kind) (fun l0 => (False.elim (l0 (replay_7034 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i491)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7036 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h : Int) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) := by
  exact (Or.elim (replay_5577 c2_kind) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_7035 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i491) t0))))

-- Checked replay of unit-resolution.
theorem replay_7037 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) : (¬ ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))) := by
  exact (Or.elim (replay_7033 c2_kind r1_kind) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_1109 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62)))) (fun t1 => (False.elim (t1 (replay_7036 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i491)))))))

-- Checked replay of unit-resolution.
theorem replay_7038 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i491 : (¬ (formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h))) (i493 : (formula_1020 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign)) (i492 : (¬ (formula_1022 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign))) : False := by
  exact (Or.elim (replay_7027 c2_depth c2_kind c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_7032 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign i491 i492) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_7037 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 i491) l1))) (fun t1 => (False.elim (t1 i493))))))

abbrev shared_expr_Repair106_7 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((formula_20 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h) ∨ (¬ (formula_1020 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign)) ∨ (formula_1022 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign))
abbrev formula_2684 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair106_7 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign)

-- Checked replay of lemma.
theorem replay_7039 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_2684 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_kind r1_node r1_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_7038 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inr (Or.inr q))))

abbrev shared_expr_Repair106_8 (r2_node r3_node : Int) : Prop := (((¬ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) ∨ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))
abbrev formula_2685 (r2_node r3_node : Int) : Prop := (shared_expr_Repair106_8 r2_node r3_node)

theorem propositional_2328 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7040 (r2_node r3_node : Int) : (formula_2685 r2_node r3_node) := by
  exact (propositional_2328 ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Repair106_9 (r2_node r3_node r3_sign : Int) : Prop := ((¬ (formula_296 r2_node r3_node r3_sign)) ∨ (¬ ((¬ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))) ∨ (¬ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_2686 (r2_node r3_node r3_sign : Int) : Prop := (shared_expr_Repair106_9 r2_node r3_node r3_sign)

theorem propositional_2329 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7041 (r2_node r3_node r3_sign : Int) : (formula_2686 r2_node r3_node r3_sign) := by
  exact (propositional_2329 ((¬ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_7042 (c3_node r2_node r3_node : Int) : (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ ((r3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair106_10 (c0_level c3_depth h r1_level r2_depth : Int) : Prop := ((¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))
abbrev formula_2687 (c0_level c3_depth h r1_level r2_depth : Int) : Prop := (shared_expr_Repair106_10 c0_level c3_depth h r1_level r2_depth)

-- Checked replay of th-lemma.
theorem replay_7043 (c0_level c3_depth h r1_level r2_depth : Int) : (formula_2687 c0_level c3_depth h r1_level r2_depth) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_2330 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7044 (c3_depth c3_kind c3_sign r1_level : Int) : ((formula_2590 c3_depth c3_kind c3_sign r1_level) ∨ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) := by
  exact (propositional_2330 (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))

theorem propositional_2331 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((¬ p8) ∨ (¬ p9))))) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p12) ∨ (¬ p13))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7045 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level))) ∨ (r1_mode ≥ (1 : Int))) := by
  exact (propositional_2331 (r1_mode ≤ (1 : Int)) (r1_mode ≥ (1 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_7046 (c0_mode r1_mode : Int) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_7047 (c0_mode c1_mode : Int) : ((¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (c1_mode ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7048 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) : (¬ (formula_345 c1_group c1_level c1_mode r0_group r0_level r0_mode)) := by
  exact (Or.elim (replay_297 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode) (fun l0 => (False.elim (l0 i495))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i494 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7049 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) : ((r0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_499 c1_group c1_level c1_mode r0_group r0_level r0_mode) (fun l0 => (False.elim ((replay_7048 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i494 i495) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7050 (c0_level c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_5668 c0_level c1_level r0_group r0_level r0_mode r1_group r1_level r1_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i357))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_7049 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i494 i495)))) (fun t2 => (False.elim (t2 i356))))))))

-- Checked replay of unit-resolution.
theorem replay_7051 (c1_kind : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) : (c1_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_2815 c1_kind) (fun l0 => (False.elim (i494 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7052 (c1_kind : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) : (c1_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_2906 c1_kind) (fun l0 => (False.elim (i494 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7053 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) : ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) := by
  exact (Or.elim (replay_2905 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (fun l0 => (False.elim (l0 i496))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7051 c1_kind i494)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_7052 c1_kind i494)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_7054 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) : ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_1088 c0_group c0_level c0_mode c1_group c1_level c1_mode) (fun l0 => (False.elim (l0 (replay_7053 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode i494 i496)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (i44 t1))))))

-- Checked replay of unit-resolution.
theorem replay_7055 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode) := by
  exact (Or.elim (replay_1089 c0_group c0_level c0_mode c1_group c1_level c1_mode) (fun l0 => (False.elim (l0 (replay_7053 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode i494 i496)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7054 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode i494 i496 i44)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7056 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (¬ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_903 c0_group c0_level c0_mode c1_group c1_level c1_mode) (fun l0 => (False.elim (l0 (replay_7055 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode i494 i496 i44)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_7050 c0_level c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i494 i357 i495 i356)))))))

-- Checked replay of unit-resolution.
theorem replay_7057 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (formula_651 c0_group c0_mode c1_group c1_mode) := by
  exact (Or.elim (replay_5684 c0_group c0_level c0_mode c1_group c1_level c1_mode) (fun l0 => (False.elim (l0 (replay_7055 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode i494 i496 i44)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_7056 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i494 i357 i496 i44 i495 i356) l1))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_7058 (c0_mode c1_mode : Int) : ((¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (c1_mode ≤ (0 : Int))) ∨ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_7059 (c1_mode r0_mode : Int) : ((¬ (r0_mode ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ∨ (c1_mode ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7060 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) : ((r0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_296 c1_group c1_level c1_mode r0_group r0_level r0_mode) (fun l0 => (False.elim ((replay_7048 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i494 i495) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7061 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) : (c1_mode ≤ (0 : Int)) := by
  exact (Or.elim (replay_7059 c1_mode r0_mode) (fun l0 => (False.elim (l0 i222))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7060 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i494 i495)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7062 (c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) : ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_7058 c0_mode c1_mode) (fun l0 => (False.elim (l0 i129))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7061 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i222 i494 i495)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7063 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (¬ ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_5631 c0_group c0_mode c1_group c1_mode) (fun l0 => (False.elim (l0 (replay_7057 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i494 i357 i496 i44 i495 i356)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_7062 c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i129 i222 i494 i495)))))))

-- Checked replay of unit-resolution.
theorem replay_7064 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_5630 c0_mode c1_mode) (fun l0 => (False.elim ((replay_7063 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i356) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7065 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (¬ (c0_mode ≥ (1 : Int))) := by
  exact (Or.elim (replay_7047 c0_mode c1_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7061 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i222 i494 i495)))) (fun t1 => (False.elim (t1 (replay_7064 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i356)))))))

-- Checked replay of unit-resolution.
theorem replay_7066 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (c0_mode ≤ (0 : Int)) := by
  exact (Or.elim (replay_1827 c0_mode) (fun l0 => l0) (fun t0 => (False.elim ((replay_7065 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i356) t0))))

-- Checked replay of unit-resolution.
theorem replay_7067 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (¬ (r1_mode ≥ (1 : Int))) := by
  exact (Or.elim (replay_7046 c0_mode r1_mode) (fun l0 => (False.elim (l0 (replay_7066 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i356)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i352))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7068 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_7045 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_7067 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i352 i356) t0))))

theorem propositional_2332 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7069 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ∨ (r1_mode ≥ (3 : Int))) := by
  exact (propositional_2332 (r1_mode ≤ (3 : Int)) (r1_mode ≥ (3 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ((c3_node % (2 : Int)) ≥ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_7070 (c0_mode r1_mode : Int) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_7071 (c0_mode : Int) : ((¬ (c0_mode ≤ (1 : Int))) ∨ (c0_mode ≤ (2 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_7072 (c0_mode c1_mode : Int) : ((c0_mode ≤ (1 : Int)) ∨ (¬ (c1_mode ≤ (1 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7073 (c0_mode c1_mode : Int) (i141 : (¬ (c0_mode ≤ (1 : Int)))) (i497 : (c1_mode ≤ (1 : Int))) : (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_7072 c0_mode c1_mode) (fun l0 => (False.elim (i141 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i497))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7074 (c0_mode c1_mode : Int) (i141 : (¬ (c0_mode ≤ (1 : Int)))) (i497 : (c1_mode ≤ (1 : Int))) : ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) := by
  exact (Or.elim (replay_5630 c0_mode c1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_7073 c0_mode c1_mode i141 i497) t0))))

-- Checked replay of th-lemma.
theorem replay_7075 (c0_mode c1_mode : Int) : ((c0_mode ≤ (1 : Int)) ∨ (¬ (c1_mode ≤ (1 : Int))) ∨ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7076 (c0_mode c1_mode : Int) (i141 : (¬ (c0_mode ≤ (1 : Int)))) (i497 : (c1_mode ≤ (1 : Int))) : ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_7075 c0_mode c1_mode) (fun l0 => (False.elim (i141 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i497))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7077 (c0_group c0_mode c1_group c1_mode : Int) (i498 : (formula_651 c0_group c0_mode c1_group c1_mode)) (i141 : (¬ (c0_mode ≤ (1 : Int)))) (i497 : (c1_mode ≤ (1 : Int))) : False := by
  exact (Or.elim (replay_5631 c0_group c0_mode c1_group c1_mode) (fun l0 => (False.elim (l0 i498))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7074 c0_mode c1_mode i141 i497)))) (fun t1 => (False.elim (t1 (replay_7076 c0_mode c1_mode i141 i497)))))))

-- Checked replay of lemma.
theorem replay_7078 (c0_group c0_mode c1_group c1_mode : Int) : ((¬ (c1_mode ≤ (1 : Int))) ∨ (¬ (formula_651 c0_group c0_mode c1_group c1_mode)) ∨ (c0_mode ≤ (1 : Int))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_7077 c0_group c0_mode c1_group c1_mode (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inr (Or.inr q))) (Classical.byContradiction (fun q => nc (Or.inl q))))

-- Checked replay of th-lemma.
theorem replay_7079 (c1_mode r0_mode : Int) : ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ∨ (c1_mode ≤ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7080 (r0_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) : (r0_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_493 r0_mode) (fun l0 => (False.elim (l0 i222))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7081 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) : (c1_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_7079 c1_mode r0_mode) (fun l0 => (False.elim (l0 (replay_7080 r0_mode i222)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7060 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i494 i495)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7082 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (c0_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_7078 c0_group c0_mode c1_group c1_mode) (fun l0 => (False.elim (l0 (replay_7081 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode i222 i494 i495)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7057 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i494 i357 i496 i44 i495 i356)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7083 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (c0_mode ≤ (2 : Int)) := by
  exact (Or.elim (replay_7071 c0_mode) (fun l0 => (False.elim (l0 (replay_7082 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i222 i494 i357 i496 i44 i495 i356)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7084 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (¬ (r1_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_7070 c0_mode r1_mode) (fun l0 => (False.elim (l0 (replay_7083 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i222 i494 i357 i496 i44 i495 i356)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i352))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7085 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_7069 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_7084 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i222 i494 i357 i496 i44 i495 i352 i356) t0))))

theorem propositional_2333 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7086 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ∨ (r1_mode ≥ (2 : Int))) := by
  exact (propositional_2333 (r1_mode ≤ (2 : Int)) (r1_mode ≥ (2 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ((c3_node % (2 : Int)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_7087 (c0_mode r1_mode : Int) : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7088 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (¬ (r1_mode ≥ (2 : Int))) := by
  exact (Or.elim (replay_7087 c0_mode r1_mode) (fun l0 => (False.elim (l0 (replay_7082 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i222 i494 i357 i496 i44 i495 i356)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i352))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7089 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_7086 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_7088 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i222 i494 i357 i496 i44 i495 i352 i356) t0))))

-- Checked replay of unit-resolution.
theorem replay_7090 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i403 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i400 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)))) := by
  exact (Or.elim (replay_6501 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (False.elim (l0 i399))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_7068 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i352 i356)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_7089 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i222 i494 i357 i496 i44 i495 i352 i356)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_7085 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i222 i494 i357 i496 i44 i495 i352 i356)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i403))) (fun t5 => (False.elim (t5 i400))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_7091 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i403 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i400 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level) := by
  exact (Or.elim (replay_6755 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (False.elim ((replay_7090 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i352 i356 i403 i400 i399) l0))) (fun t0 => t0))

theorem propositional_2334 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : (((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6))))) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ p0) ∧ (¬ p9))) ∨ p0 ∨ p9) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7092 (c2_depth c2_kind c2_sign r1_group r1_level : Int) : ((formula_1025 c2_depth c2_kind c2_sign r1_group r1_level) ∨ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∨ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) := by
  exact (propositional_2334 ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))

abbrev shared_expr_Repair106_11 (c2_depth c2_kind c2_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)))
abbrev formula_2688 (c2_depth c2_kind c2_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair106_11 c2_depth c2_kind c2_sign r1_group r1_level r1_mode)

theorem propositional_2335 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_7093 (c2_depth c2_kind c2_sign r1_group r1_level r1_mode : Int) : (formula_2688 c2_depth c2_kind c2_sign r1_group r1_level r1_mode) := by
  exact (propositional_2335 (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level))

-- Checked replay of th-lemma.
theorem replay_7094 (c0_mode r1_mode : Int) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (r1_mode ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_7095 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (r1_mode ≤ (0 : Int)) := by
  exact (Or.elim (replay_7094 c0_mode r1_mode) (fun l0 => (False.elim (l0 (replay_7066 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i356)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i352))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7096 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i119 : (r1_mode ≥ (0 : Int))) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i499 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)))) : (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)) := by
  exact (Or.elim (replay_7093 c2_depth c2_kind c2_sign r1_group r1_level r1_mode) (fun l0 => (False.elim (l0 i499))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i119))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_7095 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i352 i356)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_7097 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i119 : (r1_mode ≥ (0 : Int))) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i500 : (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i499 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)))) : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) := by
  exact (Or.elim (replay_7092 c2_depth c2_kind c2_sign r1_group r1_level) (fun l0 => (False.elim ((replay_7096 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i119 i129 i222 i494 i357 i496 i44 i495 i352 i356 i499) l0))) (fun t0 => (Or.elim t0 (fun l1 => (Or.elim l1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t1 => (False.elim (i500 t1))))))

-- Checked replay of unit-resolution.
theorem replay_7098 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i119 : (r1_mode ≥ (0 : Int))) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i500 : (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i499 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)))) (i403 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i400 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level)) := by
  exact (Or.elim (replay_6754 c3_depth c3_kind c3_sign r1_group r1_level) (fun l0 => (False.elim (l0 (replay_7091 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i129 i222 i494 i357 i496 i44 i495 i352 i356 i403 i400 i399)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_7097 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i119 i129 i222 i494 i500 i357 i496 i44 i495 i352 i356 i499)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_7099 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i119 : (r1_mode ≥ (0 : Int))) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i500 : (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i499 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)))) (i403 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i400 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) := by
  exact (Or.elim (replay_7044 c3_depth c3_kind c3_sign r1_level) (fun l0 => (False.elim ((replay_7098 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i119 i129 i222 i494 i500 i357 i496 i44 i495 i352 i356 i499 i403 i400 i399) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_7100 (c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) (i119 : (r1_mode ≥ (0 : Int))) (i129 : (c0_mode ≥ (0 : Int))) (i222 : (r0_mode ≤ (0 : Int))) (i494 : (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) (i500 : (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) (i357 : (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (i496 : (formula_1444 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (i44 : (¬ (c0_mode ≥ (4 : Int)))) (i495 : (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) (i352 : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) (i356 : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i499 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_1025 c2_depth c2_kind c2_sign r1_group r1_level)))) (i403 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i400 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_6815 c3_depth r1_level) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_7099 c0_group c0_level c0_mode c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_kind c2_sign c3_depth c3_kind c3_node c3_sign r0_group r0_level r0_mode r1_group r1_level r1_mode i119 i129 i222 i494 i500 i357 i496 i44 i495 i352 i356 i499 i403 i400 i399)))))

end H4Formal.Generated.Repair
