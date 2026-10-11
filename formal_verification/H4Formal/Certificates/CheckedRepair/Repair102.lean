import H4Formal.Certificates.CheckedRepair.Repair101

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of unit-resolution.
theorem replay_6630 (c2_depth c3_depth c3_node c3_sign h r2_depth r3_depth r3_node r3_sign : Int) (i418 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) := by
  exact (Or.elim (replay_6583 c2_depth c3_depth r2_depth r3_depth) (fun l0 => (False.elim (i418 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i411))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6629 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i426)))) (fun t2 => t2))))))

theorem propositional_2253 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6631 (c3_node c3_sign r3_node r3_sign : Int) : (((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∨ (c3_sign ≤ (0 : Int))) := by
  exact (propositional_2253 (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6632 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_6001 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim (i426 l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))))

-- Checked replay of unit-resolution.
theorem replay_6633 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i414 : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) (i428 : (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) := by
  exact (Or.elim (replay_6002 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim (l0 (replay_6632 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i426)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i414))) (fun t2 => (False.elim (t2 i428))))))))

-- Checked replay of unit-resolution.
theorem replay_6634 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i414 : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) (i428 : (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : (c3_sign ≤ (0 : Int)) := by
  exact (Or.elim (replay_6631 c3_node c3_sign r3_node r3_sign) (fun l0 => (False.elim ((replay_6633 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i414 i428 i426) l0))) (fun t0 => t0))

theorem propositional_2254 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6635 (c3_node c3_sign r3_node r3_sign : Int) : (((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∨ (c3_sign ≥ (0 : Int))) := by
  exact (propositional_2254 (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6636 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i414 : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) (i428 : (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : (c3_sign ≥ (0 : Int)) := by
  exact (Or.elim (replay_6635 c3_node c3_sign r3_node r3_sign) (fun l0 => (False.elim ((replay_6633 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i414 i428 i426) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6637 (c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign : Int) (i429 : ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i414 : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) (i428 : (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : (¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) := by
  exact (Or.elim (replay_5995 c3_node c3_sign r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6634 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i414 i428 i426)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6636 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i414 i428 i426)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i61))) (fun t3 => (False.elim (t3 i429))))))))))

-- Checked replay of unit-resolution.
theorem replay_6638 (c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign : Int) (i429 : ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i414 : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) (i428 : (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : ((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign))) := by
  exact (Or.elim (replay_5994 c3_node c3_sign r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_6637 c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign i429 i61 i414 i428 i426) t0))))

-- Checked replay of unit-resolution.
theorem replay_6639 (c2_depth c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i429 : ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i418 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (i417 : ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i427 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i414 : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) (i428 : (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)) (i426 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))))) : False := by
  exact (Or.elim (replay_6022 c3_depth c3_node c3_sign r2_depth r2_node r2_sign) (fun l0 => (False.elim (l0 i371))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6628 c2_depth c3_depth c3_node c3_sign h r2_depth r3_depth r3_node r3_sign i417 i427 i426)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6630 c2_depth c3_depth c3_node c3_sign h r2_depth r3_depth r3_node r3_sign i418 i411 i426)))) (fun t2 => (False.elim (t2 (replay_6638 c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign i429 i61 i414 i428 i426)))))))))

abbrev shared_expr_Repair102_0 (c2_depth c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))) ∨ (¬ (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))) ∨ (¬ (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)))
abbrev formula_2622 (c2_depth c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair102_0 c2_depth c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_6640 (c2_depth c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : (formula_2622 c2_depth c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6639 c2_depth c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (fun q => nc (Or.inl q)))

theorem propositional_2255 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6641 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : ((formula_868 c0_node c0_sign h r1_depth r1_node r1_sign) ∨ (r1_sign ≥ (1 : Int))) := by
  exact (propositional_2255 ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)))

abbrev shared_expr_Repair102_1 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∨ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)))
abbrev formula_2623 (c0_node c0_sign r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_1 c0_node c0_sign r1_node r1_sign)

theorem propositional_2256 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p4) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6642 (c0_node c0_sign r1_node r1_sign : Int) : (formula_2623 c0_node c0_sign r1_node r1_sign) := by
  exact (propositional_2256 (r1_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)))

abbrev shared_expr_Repair102_2 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) ∨ (¬ (formula_867 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_868 c0_node c0_sign h r1_depth r1_node r1_sign)))
abbrev formula_2624 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_2 c0_node c0_sign h r1_depth r1_node r1_sign)

theorem propositional_2257 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6643 (c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_2624 c0_node c0_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2257 ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) (formula_867 c0_node c0_sign h r1_depth r1_node r1_sign) (formula_868 c0_node c0_sign h r1_depth r1_node r1_sign))

abbrev shared_expr_Repair102_3 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign))) ∨ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign))
abbrev formula_2625 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_3 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)

theorem propositional_2258 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6644 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_2625 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2258 ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign))

abbrev shared_expr_Repair102_4 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign)))) ∨ (¬ (formula_872 c0_depth c0_node c0_sign r1_depth r1_node r1_sign)))
abbrev formula_2626 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_4 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)

theorem propositional_2259 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6645 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_2626 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2259 ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign))) (formula_872 c0_depth c0_node c0_sign r1_depth r1_node r1_sign))

theorem propositional_2260 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ p6))) ∨ (¬ p7))) ∨ (¬ (p8 ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ ((¬ p11) ∨ (¬ p12))) ∨ (¬ p6)))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6646 (c0_depth c0_node c0_sign r1_depth r1_node r1_sign : Int) : ((formula_872 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) := by
  exact (propositional_2260 ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ((c0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)))

abbrev shared_expr_Repair102_5 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : Prop := (((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))))
abbrev formula_2627 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : Prop := (shared_expr_Repair102_5 c0_depth c2_depth c3_depth r1_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_6647 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : (formula_2627 c0_depth c2_depth c3_depth r1_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair102_6 (c3_node c3_sign r1_node r1_sign : Int) : Prop := ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2628 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_6 c3_node c3_sign r1_node r1_sign)

abbrev shared_expr_Repair102_7 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))))
abbrev formula_2629 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_7 c3_node c3_sign r1_node r1_sign)

abbrev shared_expr_Repair102_8 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ ((¬ (formula_2628 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2629 c3_node c3_sign r1_node r1_sign)))))
abbrev formula_2630 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_8 c3_depth c3_node c3_sign r1_depth r1_node r1_sign)

theorem propositional_2261 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ p6))) ∨ (¬ p7))) ∨ (¬ (p8 ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ ((¬ p11) ∨ (¬ p12))) ∨ (¬ p6)))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6648 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : ((formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) ∨ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := by
  exact (propositional_2261 ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6649 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_6648 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) (fun l0 => (False.elim (i430 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6650 (c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) := by
  exact (Or.elim (replay_6647 c0_depth c2_depth c3_depth r1_depth r3_depth) (fun l0 => (False.elim (i432 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i411))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6649 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i430)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (i431 l3))) (fun t3 => t3))))))))

-- Checked replay of unit-resolution.
theorem replay_6651 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : (formula_872 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) := by
  exact (Or.elim (replay_6646 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6650 c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth i431 i430 i411 i432) t0))))

-- Checked replay of unit-resolution.
theorem replay_6652 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign)))) := by
  exact (Or.elim (replay_6645 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim (l0 i433))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_6651 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth i431 i430 i411 i432)))))))

-- Checked replay of unit-resolution.
theorem replay_6653 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign) := by
  exact (Or.elim (replay_6644 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim ((replay_6652 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth i431 i433 i430 i411 i432) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))))

-- Checked replay of unit-resolution.
theorem replay_6654 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i435 : (formula_867 c0_node c0_sign h r1_depth r1_node r1_sign)) (i434 : (formula_868 c0_node c0_sign h r1_depth r1_node r1_sign)) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int))))) := by
  exact (Or.elim (replay_6643 c0_node c0_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim (l0 (replay_6653 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth i431 i433 i430 i411 i432)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i435))) (fun t2 => (False.elim (t2 i434))))))))

-- Checked replay of unit-resolution.
theorem replay_6655 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i435 : (formula_867 c0_node c0_sign h r1_depth r1_node r1_sign)) (i434 : (formula_868 c0_node c0_sign h r1_depth r1_node r1_sign)) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_6642 c0_node c0_sign r1_node r1_sign) (fun l0 => (False.elim ((replay_6654 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth i431 i435 i434 i433 i430 i411 i432) l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_6656 (c0_depth c2_depth r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair102_9 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : Prop := (((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∨ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)))
abbrev formula_2631 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : Prop := (shared_expr_Repair102_9 c0_depth c2_depth c3_depth r1_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_6657 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : (formula_2631 c0_depth c2_depth c3_depth r1_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6658 (c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_6657 c0_depth c2_depth c3_depth r1_depth r3_depth) (fun l0 => (False.elim (i432 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i411))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6649 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i430)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (i431 l3))) (fun t3 => t3))))))))

-- Checked replay of unit-resolution.
theorem replay_6659 (c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth : Int) (i437 : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_6656 c0_depth c2_depth r1_depth) (fun l0 => (False.elim (l0 (replay_6658 c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth i431 i430 i411 i432)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i437))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_6660 (c0_depth c2_depth r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∨ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair102_10 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : Prop := ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))
abbrev formula_2632 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : Prop := (shared_expr_Repair102_10 c0_depth c2_depth c3_depth r1_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_6661 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) : (formula_2632 c0_depth c2_depth c3_depth r1_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_6662 (c3_depth r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_2262 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ p6))) ∨ (¬ p7))) ∨ (¬ (p8 ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ ((¬ p11) ∨ (¬ p12))) ∨ (¬ p6)))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6663 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : ((formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) ∨ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) := by
  exact (propositional_2262 ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6664 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) := by
  exact (Or.elim (replay_6663 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) (fun l0 => (False.elim (i430 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6665 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_6662 c3_depth r1_depth) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_6664 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i430)))))

-- Checked replay of unit-resolution.
theorem replay_6666 (c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth : Int) (i437 : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i427 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i438 : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) : ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_6661 c0_depth c2_depth c3_depth r1_depth r3_depth) (fun l0 => (False.elim (l0 i438))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i427))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim ((replay_6665 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i430) l2))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i437))) (fun t3 => t3))))))))

-- Checked replay of unit-resolution.
theorem replay_6667 (c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth : Int) (i437 : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i427 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i438 : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) : ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_6660 c0_depth c2_depth r1_depth) (fun l0 => (False.elim (l0 (replay_6666 c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth i437 i430 i427 i438)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i431 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6668 (c0_depth c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i437 : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i166 : ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i427 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i438 : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) : (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)) := by
  exact (Or.elim (replay_2541 c2_depth c2_node c2_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim (l0 i166))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6659 c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth i437 i431 i430 i411 i432)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6667 c0_depth c2_depth c3_depth c3_node c3_sign r1_depth r1_node r1_sign r3_depth i437 i431 i430 i427 i438)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_6669 (c0_depth c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i437 : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i166 : ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)))) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i427 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i438 : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) : ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) := by
  exact (Or.elim (replay_2540 c2_node c2_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim ((replay_6668 c0_depth c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth i437 i431 i166 i430 i411 i427 i432 i438) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))))

theorem propositional_2263 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6670 (r1_sign : Int) : (((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))) ∨ (r1_sign ≤ (0 : Int))) := by
  exact (propositional_2263 (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)))

abbrev shared_expr_Repair102_11 (r1_sign : Int) : Prop := ((¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))
abbrev formula_2633 (r1_sign : Int) : Prop := (shared_expr_Repair102_11 r1_sign)

theorem propositional_2264 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6671 (r1_sign : Int) : (formula_2633 r1_sign) := by
  exact (propositional_2264 ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))) ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))

theorem propositional_2265 (p0 p1 p2 p3 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6672 (c3_node c3_sign r1_node r1_sign : Int) : ((formula_2628 c3_node c3_sign r1_node r1_sign) ∨ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) := by
  exact (propositional_2265 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Repair102_12 (c3_node c3_sign r1_node r1_sign : Int) : Prop := ((¬ ((¬ (formula_2628 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2629 c3_node c3_sign r1_node r1_sign)))) ∨ (¬ (formula_2628 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2629 c3_node c3_sign r1_node r1_sign)))
abbrev formula_2634 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_12 c3_node c3_sign r1_node r1_sign)

theorem propositional_2266 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6673 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2634 c3_node c3_sign r1_node r1_sign) := by
  exact (propositional_2266 (formula_2628 c3_node c3_sign r1_node r1_sign) (formula_2629 c3_node c3_sign r1_node r1_sign))

theorem propositional_2267 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6674 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : ((formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) ∨ ((¬ (formula_2628 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2629 c3_node c3_sign r1_node r1_sign)))) := by
  exact (propositional_2267 ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((¬ (formula_2628 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2629 c3_node c3_sign r1_node r1_sign))))

-- Checked replay of unit-resolution.
theorem replay_6675 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : ((¬ (formula_2628 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2629 c3_node c3_sign r1_node r1_sign))) := by
  exact (Or.elim (replay_6674 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) (fun l0 => (False.elim (i430 l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_6676 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i439 : (formula_2629 c3_node c3_sign r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : (¬ (formula_2628 c3_node c3_sign r1_node r1_sign)) := by
  exact (Or.elim (replay_6673 c3_node c3_sign r1_node r1_sign) (fun l0 => (False.elim (l0 (replay_6675 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i430)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 i439))))))

-- Checked replay of unit-resolution.
theorem replay_6677 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i439 : (formula_2629 c3_node c3_sign r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) := by
  exact (Or.elim (replay_6672 c3_node c3_sign r1_node r1_sign) (fun l0 => (False.elim ((replay_6676 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i439 i430) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_6678 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i440 : ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) (i439 : (formula_2629 c3_node c3_sign r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) := by
  exact (Or.elim (replay_6671 r1_sign) (fun l0 => (False.elim (l0 (replay_6677 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i439 i430)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 i440))))))

-- Checked replay of unit-resolution.
theorem replay_6679 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i440 : ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) (i439 : (formula_2629 c3_node c3_sign r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : (r1_sign ≤ (0 : Int)) := by
  exact (Or.elim (replay_6670 r1_sign) (fun l0 => (False.elim ((replay_6678 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i440 i439 i430) l0))) (fun t0 => t0))

theorem propositional_2268 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6680 (r1_sign : Int) : (((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))) ∨ (r1_sign ≥ (0 : Int))) := by
  exact (propositional_2268 (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6681 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i440 : ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) (i439 : (formula_2629 c3_node c3_sign r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) : (r1_sign ≥ (0 : Int)) := by
  exact (Or.elim (replay_6680 r1_sign) (fun l0 => (False.elim ((replay_6678 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i440 i439 i430) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6682 (c0_depth c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i440 : ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) (i170 : (c2_sign ≥ (0 : Int))) (i169 : (c2_sign ≤ (0 : Int))) (i437 : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i166 : ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)))) (i439 : (formula_2629 c3_node c3_sign r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i427 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i438 : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) : (¬ ((r1_node + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_2560 c2_node c2_sign r1_node r1_sign) (fun l0 => (False.elim (l0 (replay_6669 c0_depth c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth i437 i431 i166 i430 i411 i427 i432 i438)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6681 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i440 i439 i430)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6679 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i440 i439 i430)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i169))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i170))) (fun t4 => t4))))))))))

-- Checked replay of th-lemma.
theorem replay_6683 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) (i436 : (¬ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) (i440 : ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) (i170 : (c2_sign ≥ (0 : Int))) (i169 : (c2_sign ≤ (0 : Int))) (i437 : ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i435 : (formula_867 c0_node c0_sign h r1_depth r1_node r1_sign)) (i434 : (formula_868 c0_node c0_sign h r1_depth r1_node r1_sign)) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i166 : ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)))) (i439 : (formula_2629 c3_node c3_sign r1_node r1_sign)) (i430 : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i427 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) (i432 : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i438 : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) : False := by
  classical
  have k0 := (replay_6655 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth i431 i435 i434 i433 i430 i411 i432)
  have k1 := i436
  have k2 := (replay_6682 c0_depth c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth i440 i170 i169 i437 i431 i166 i439 i430 i411 i427 i432 i438)
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair102_13 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) : Prop := ((formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) ∨ ((c0_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1016 c2_node c2_sign h r1_depth r1_node r1_sign)))) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∨ (¬ (formula_868 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_867 c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) ∨ (¬ (formula_2629 c3_node c3_sign r1_node r1_sign)))
abbrev formula_2635 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) : Prop := (shared_expr_Repair102_13 c0_depth c0_node c0_sign c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth)

-- Checked replay of lemma.
theorem replay_6684 (c0_depth c0_node c0_sign c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth : Int) : (formula_2635 c0_depth c0_node c0_sign c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6683 c0_depth c0_node c0_sign c2_depth c2_node c2_sign c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth (fun q => nc (Or.inr (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))))))))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))

theorem propositional_2269 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6685 (r1_sign : Int) : (((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ∨ (r1_sign ≥ (2 : Int))) := by
  exact (propositional_2269 (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)))

abbrev shared_expr_Repair102_14 (r1_sign : Int) : Prop := ((¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))))
abbrev formula_2636 (r1_sign : Int) : Prop := (shared_expr_Repair102_14 r1_sign)

theorem propositional_2270 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6686 (r1_sign : Int) : (formula_2636 r1_sign) := by
  exact (propositional_2270 ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))) ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))

-- Checked replay of th-lemma.
theorem replay_6687 (r1_sign : Int) : ((r1_sign ≥ (1 : Int)) ∨ (¬ (r1_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6688 (r1_sign : Int) (i441 : (r1_sign ≥ (2 : Int))) : (r1_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_6687 r1_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 i441))))

-- Checked replay of unit-resolution.
theorem replay_6689 (r1_sign : Int) (i441 : (r1_sign ≥ (2 : Int))) : (¬ (r1_sign ≤ (0 : Int))) := by
  exact (Or.elim (replay_3178 r1_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_6688 r1_sign i441)))))

-- Checked replay of unit-resolution.
theorem replay_6690 (r1_sign : Int) (i441 : (r1_sign ≥ (2 : Int))) : ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int)))) := by
  exact (Or.elim (replay_6670 r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_6689 r1_sign i441) t0))))

theorem propositional_2271 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6691 (r1_sign : Int) : (((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))) ∨ (r1_sign ≤ (1 : Int))) := by
  exact (propositional_2271 (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_6692 (r1_sign : Int) : ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6693 (r1_sign : Int) (i441 : (r1_sign ≥ (2 : Int))) : (¬ (r1_sign ≤ (1 : Int))) := by
  exact (Or.elim (replay_6692 r1_sign) (fun l0 => l0) (fun t0 => (False.elim (t0 i441))))

-- Checked replay of unit-resolution.
theorem replay_6694 (r1_sign : Int) (i441 : (r1_sign ≥ (2 : Int))) : ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))) := by
  exact (Or.elim (replay_6691 r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_6693 r1_sign i441) t0))))

-- Checked replay of unit-resolution.
theorem replay_6695 (r1_sign : Int) (i441 : (r1_sign ≥ (2 : Int))) (i442 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))))) : False := by
  exact (Or.elim (replay_6686 r1_sign) (fun l0 => (False.elim (l0 i442))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6690 r1_sign i441)))) (fun t1 => (False.elim (t1 (replay_6694 r1_sign i441)))))))

-- Checked replay of lemma.
theorem replay_6696 (r1_sign : Int) : ((¬ (r1_sign ≥ (2 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6695 r1_sign (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr q))))

abbrev shared_expr_Repair102_15 (h r1_depth r1_sign : Int) : Prop := ((¬ (formula_638 h r1_depth r1_sign)) ∨ (¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))))) ∨ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))))
abbrev formula_2637 (h r1_depth r1_sign : Int) : Prop := (shared_expr_Repair102_15 h r1_depth r1_sign)

theorem propositional_2272 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6697 (h r1_depth r1_sign : Int) : (formula_2637 h r1_depth r1_sign) := by
  exact (propositional_2272 ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))) ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_6698 (h r1_depth r2_depth : Int) : (((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair102_16 (c0_depth c2_depth r1_depth r2_depth : Int) : Prop := ((¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))
abbrev formula_2638 (c0_depth c2_depth r1_depth r2_depth : Int) : Prop := (shared_expr_Repair102_16 c0_depth c2_depth r1_depth r2_depth)

-- Checked replay of th-lemma.
theorem replay_6699 (c0_depth c2_depth r1_depth r2_depth : Int) : (formula_2638 c0_depth c2_depth r1_depth r2_depth) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair102_17 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))) ∨ (¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev formula_2639 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_17 c3_node c3_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Repair102_18 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∨ ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ∨ (¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))
abbrev formula_2640 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_18 c3_node c3_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Repair102_19 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2639 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_2640 c3_node c3_sign h r1_depth r1_node r1_sign)))
abbrev formula_2641 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_19 c3_node c3_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Repair102_20 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2641 c3_node c3_sign h r1_depth r1_node r1_sign)))) ∨ (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign)))
abbrev formula_2642 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_20 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)

abbrev shared_expr_Repair102_21 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (formula_2642 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2641 c3_node c3_sign h r1_depth r1_node r1_sign)))) ∨ (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign)))
abbrev formula_2643 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_21 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)

theorem propositional_2273 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6700 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2643 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2273 ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2641 c3_node c3_sign h r1_depth r1_node r1_sign))) (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign))

abbrev shared_expr_Repair102_22 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2641 c3_node c3_sign h r1_depth r1_node r1_sign))) ∨ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))
abbrev formula_2644 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_22 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)

theorem propositional_2274 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ (¬ ((¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p6))) ∨ (¬ (p7 ∨ p13 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17)))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6701 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2644 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2274 ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)))

abbrev shared_expr_Repair102_23 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign))) ∨ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)))
abbrev formula_2645 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair102_23 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)

theorem propositional_2275 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ (¬ ((¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p6))) ∨ (¬ (p7 ∨ p13 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17)))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6702 (c0_depth c0_node c0_sign h r1_depth r1_node r1_sign : Int) : (formula_2645 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2275 ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * c0_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) (c0_sign ≤ (2 : Int)) (c0_sign ≥ (2 : Int)) ((r1_node + ((-1 : Int) * c0_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_6703 (c0_depth c3_depth r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6704 (c0_depth c3_depth r1_depth : Int) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i443 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) : (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) := by
  exact (Or.elim (replay_6703 c0_depth c3_depth r1_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i443))) (fun t1 => (False.elim (t1 i444))))))

-- Checked replay of unit-resolution.
theorem replay_6705 (c0_depth c0_node c0_sign c3_depth r1_depth r1_node r1_sign : Int) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i443 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) : (formula_872 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) := by
  exact (Or.elim (replay_6646 c0_depth c0_node c0_sign r1_depth r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6704 c0_depth c3_depth r1_depth i444 i443) t0))))

-- Checked replay of unit-resolution.
theorem replay_6706 (c0_depth c0_node c0_sign c3_depth h r1_depth r1_node r1_sign : Int) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i443 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) : (¬ ((¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ (¬ (formula_869 c0_node c0_sign h r1_depth r1_node r1_sign)))) := by
  exact (Or.elim (replay_6645 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim (l0 i433))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_6705 c0_depth c0_node c0_sign c3_depth r1_depth r1_node r1_sign i444 i443)))))))

abbrev shared_expr_Repair102_24 (c0_depth c2_depth r1_depth r3_depth : Int) : Prop := ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) ∨ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∨ ((r1_depth + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))
abbrev formula_2646 (c0_depth c2_depth r1_depth r3_depth : Int) : Prop := (shared_expr_Repair102_24 c0_depth c2_depth r1_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_6707 (c0_depth c2_depth r1_depth r3_depth : Int) : (formula_2646 c0_depth c2_depth r1_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_6708 (c3_depth r1_depth r3_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6709 (c3_depth r1_depth r3_depth : Int) (i443 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) (i445 : ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) : (¬ ((r1_depth + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_6708 c3_depth r1_depth r3_depth) (fun l0 => (False.elim (l0 i443))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i445))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6710 (c0_depth c2_depth c3_depth r1_depth r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i443 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i445 : ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) : (¬ ((r1_depth + ((-1 : Int) * c0_depth)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_6707 c0_depth c2_depth r1_depth r3_depth) (fun l0 => (False.elim (l0 i411))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (i431 l2))) (fun t2 => (False.elim ((replay_6709 c3_depth r1_depth r3_depth i443 i445) t2))))))))

-- Checked replay of unit-resolution.
theorem replay_6711 (c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i443 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i445 : ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) : False := by
  exact (Or.elim (replay_6702 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim ((replay_6706 c0_depth c0_node c0_sign c3_depth h r1_depth r1_node r1_sign i444 i433 i443) l0))) (fun t0 => (False.elim ((replay_6710 c0_depth c2_depth c3_depth r1_depth r3_depth i431 i443 i411 i445) t0))))

abbrev shared_expr_Repair102_25 (c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth : Int) : Prop := ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))
abbrev formula_2647 (c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth : Int) : Prop := (shared_expr_Repair102_25 c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth)

-- Checked replay of lemma.
theorem replay_6712 (c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth : Int) : (formula_2647 c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6711 c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))

-- Checked replay of unit-resolution.
theorem replay_6713 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) (i446 : (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))) : ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) := by
  exact (Or.elim (replay_6417 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) (fun l0 => (False.elim (i446 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6714 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i446 : (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))) : (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_6712 c0_depth c0_node c0_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i433))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i411))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (i431 l3))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_6713 c3_depth c3_node c3_sign r3_depth r3_node r3_sign i446)))) (fun t4 => (False.elim (t4 i444))))))))))))

-- Checked replay of unit-resolution.
theorem replay_6715 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i446 : (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))) : ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2641 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
  exact (Or.elim (replay_6701 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6714 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth r3_node r3_sign i431 i444 i433 i411 i446) t0))))

-- Checked replay of unit-resolution.
theorem replay_6716 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i447 : (formula_2642 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i446 : (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))) : (¬ (formula_2630 c3_depth c3_node c3_sign r1_depth r1_node r1_sign)) := by
  exact (Or.elim (replay_6700 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) (fun l0 => (False.elim (l0 i447))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6715 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth r3_node r3_sign i431 i444 i433 i411 i446)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6717 (c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i431 : (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≤ (-1 : Int)))) (i444 : ((c0_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) (i433 : (formula_873 c0_depth c0_node c0_sign h r1_depth r1_node r1_sign)) (i447 : (formula_2642 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)) (i411 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i446 : (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))) : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_6648 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) (fun l0 => (False.elim ((replay_6716 c0_depth c0_node c0_sign c2_depth c3_depth c3_node c3_sign h r1_depth r1_node r1_sign r3_depth r3_node r3_sign i431 i444 i433 i447 i411 i446) l0))) (fun t0 => t0))

end H4Formal.Generated.Repair
