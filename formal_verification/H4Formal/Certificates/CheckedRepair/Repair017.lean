import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair016

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of unit-resolution.
theorem replay_630 (c0_level r2_depth r2_kind r2_sign : Int) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (formula_64 c0_level r2_depth r2_kind r2_sign) := by
  exact (Or.elim (replay_629 c0_level r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim ((replay_605 c0_level r2_depth i51) t0))))

-- Checked replay of unit-resolution.
theorem replay_631 (c0_group c0_level r2_depth r2_kind r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_628 c0_group c0_level r2_depth r2_kind r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_630 c0_level r2_depth r2_kind r2_sign i51)))))))

-- Checked replay of unit-resolution.
theorem replay_632 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign))) := by
  exact (Or.elim (replay_627 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_631 c0_group c0_level r2_depth r2_kind r2_sign i50 i51) t0))))

-- Checked replay of unit-resolution.
theorem replay_633 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)))) := by
  exact (Or.elim (replay_600 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i52))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_632 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i50 i51)))) (fun t1 => (Or.elim t1 (fun l2 => l2) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_614 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_608 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_620 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51)))) (fun t5 => (False.elim (t5 (replay_626 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51)))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_634 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (c0_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_599 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_633 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_635 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (c0_mode ≥ (2 : Int))) := by
  exact (Or.elim (replay_598 c0_mode) (fun l0 => (False.elim (l0 (replay_634 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_636 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (c0_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_597 c0_mode) (fun l0 => (False.elim ((replay_635 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_637 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (c0_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_596 c0_mode) (fun l0 => (False.elim ((replay_636 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => t0))

theorem propositional_442 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_638 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (c0_mode ≥ (2 : Int))) := by
  exact (propositional_442 (c0_mode ≤ (2 : Int)) (c0_mode ≥ (2 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_639 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_571 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_638 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_635 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) t0))))

theorem propositional_443 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_640 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (c0_mode ≥ (3 : Int))) := by
  exact (propositional_443 (c0_mode ≤ (3 : Int)) (c0_mode ≥ (3 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_641 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_573 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_640 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_636 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) t0))))

theorem propositional_444 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p6))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_642 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : (((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign))) ∨ (c0_mode ≤ (0 : Int))) := by
  exact (propositional_444 (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_643 (c0_mode : Int) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_445 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p8))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_644 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign))) ∨ (c0_mode ≥ (1 : Int))) := by
  exact (propositional_445 (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_645 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (c0_mode ≥ (1 : Int)) := by
  exact (Or.elim (replay_644 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_633 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_646 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (c0_mode ≤ (0 : Int))) := by
  exact (Or.elim (replay_643 c0_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_645 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52)))))

-- Checked replay of unit-resolution.
theorem replay_647 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_566 c0_group c0_level r1_depth r1_kind r1_sign))) := by
  exact (Or.elim (replay_642 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_646 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) t0))))

-- Checked replay of unit-resolution.
theorem replay_648 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i45 : (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_569 c0_group c0_level r1_depth r1_kind r1_sign)))) := by
  exact (Or.elim (replay_595 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_637 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i45))) (fun t1 => (Or.elim t1 (fun l2 => l2) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_639 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i50 i51 i52)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_641 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i50 i51 i52)))) (fun t4 => (False.elim (t4 (replay_647 c0_group c0_level c0_mode r1_depth r1_kind r1_sign r2_depth r2_kind r2_node r2_sign i50 i51 i52)))))))))))))

-- Checked replay of unit-resolution.
theorem replay_649 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i45 : (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (formula_569 c0_group c0_level r1_depth r1_kind r1_sign) := by
  exact (Or.elim (replay_542 c0_group c0_level c0_mode r1_depth r1_kind r1_sign) (fun l0 => (False.elim ((replay_648 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i50 i45 i51 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_650 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i45 : (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_568 c0_level r1_depth r1_kind r1_sign)) := by
  exact (Or.elim (replay_587 c0_group c0_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim (l0 (replay_649 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i50 i45 i51 i52)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_651 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i45 : (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) := by
  exact (Or.elim (replay_586 c0_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim ((replay_650 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i50 i45 i51 i52) l0))) (fun t0 => t0))

theorem propositional_446 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7)))))) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_652 (c0_level r2_depth r2_kind r2_sign : Int) : ((formula_67 c0_level r2_depth r2_kind r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) := by
  exact (propositional_446 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_653 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (formula_71 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_603 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (i53 t0))))

-- Checked replay of unit-resolution.
theorem replay_654 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_602 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_653 c0_level r2_depth r2_kind r2_node r2_sign i53)))))))

-- Checked replay of unit-resolution.
theorem replay_655 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_601 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_654 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i53) t0))))

-- Checked replay of unit-resolution.
theorem replay_656 (c0_level r2_depth r2_kind r2_sign : Int) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (formula_64 c0_level r2_depth r2_kind r2_sign) := by
  exact (Or.elim (replay_629 c0_level r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim (i53 t0))))

-- Checked replay of unit-resolution.
theorem replay_657 (c0_group c0_level r2_depth r2_kind r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_628 c0_group c0_level r2_depth r2_kind r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_656 c0_level r2_depth r2_kind r2_sign i53)))))))

-- Checked replay of unit-resolution.
theorem replay_658 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign))) := by
  exact (Or.elim (replay_627 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_657 c0_group c0_level r2_depth r2_kind r2_sign i50 i53) t0))))

-- Checked replay of unit-resolution.
theorem replay_659 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) (i57 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)))) (i54 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) (i55 : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) (i56 : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : False := by
  exact (Or.elim (replay_600 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i52))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_658 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i50 i53)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i57))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i54))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_655 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i53)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i55))) (fun t5 => (False.elim (t5 i56))))))))))))))

abbrev shared_expr_Repair017_0 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ∨ (¬ (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)))) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))
abbrev formula_589 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_0 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_660 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (formula_589 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_659 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

theorem propositional_447 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_661 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign))) ∨ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)) := by
  exact (propositional_447 (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (formula_68 c0_group c0_level r2_depth r2_kind r2_sign))

theorem propositional_448 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_662 (c0_group c0_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_67 c0_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_448 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) (formula_67 c0_level r2_depth r2_kind r2_sign))

-- Checked replay of unit-resolution.
theorem replay_663 (c0_group c0_level r2_depth r2_kind r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i58 : (formula_67 c0_level r2_depth r2_kind r2_sign)) : (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_662 c0_group c0_level r2_depth r2_kind r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 i58))))))

-- Checked replay of unit-resolution.
theorem replay_664 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i58 : (formula_67 c0_level r2_depth r2_kind r2_sign)) : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign))) := by
  exact (Or.elim (replay_661 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_663 c0_group c0_level r2_depth r2_kind r2_sign i50 i58) t0))))

-- Checked replay of unit-resolution.
theorem replay_665 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (formula_73 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_617 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (i53 t0))))

-- Checked replay of unit-resolution.
theorem replay_666 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_616 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_665 c0_level r2_depth r2_kind r2_node r2_sign i53)))))))

-- Checked replay of unit-resolution.
theorem replay_667 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_615 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_666 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i53) t0))))

-- Checked replay of unit-resolution.
theorem replay_668 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (formula_75 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_623 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (i53 t0))))

-- Checked replay of unit-resolution.
theorem replay_669 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_622 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_668 c0_level r2_depth r2_kind r2_node r2_sign i53)))))))

-- Checked replay of unit-resolution.
theorem replay_670 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_621 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_669 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i53) t0))))

-- Checked replay of unit-resolution.
theorem replay_671 (c0_level r2_depth r2_kind r2_node r2_sign : Int) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (formula_69 c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_611 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (i53 t0))))

-- Checked replay of unit-resolution.
theorem replay_672 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_610 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i50 l1))) (fun t1 => (False.elim (t1 (replay_671 c0_level r2_depth r2_kind r2_node r2_sign i53)))))))

-- Checked replay of unit-resolution.
theorem replay_673 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_609 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_672 c0_group c0_level r2_depth r2_kind r2_node r2_sign i50 i53) t0))))

-- Checked replay of unit-resolution.
theorem replay_674 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i53 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) (i58 : (formula_67 c0_level r2_depth r2_kind r2_sign)) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : False := by
  exact (Or.elim (replay_660 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (i53 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i52))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_673 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i53)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_667 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i53)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_670 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i53)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_664 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i50 i58)))) (fun t5 => (False.elim (i50 t5))))))))))))))

abbrev shared_expr_Repair017_1 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ∨ (¬ (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ (formula_67 c0_level r2_depth r2_kind r2_sign)))
abbrev formula_590 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_1 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_675 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (formula_590 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_674 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign (fun q => nc (Or.inl q)) (fun q => nc (Or.inr (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))))

-- Checked replay of unit-resolution.
theorem replay_676 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_67 c0_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_675 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (i50 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_605 c0_level r2_depth i51) l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i52))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_677 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) := by
  exact (Or.elim (replay_652 c0_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_676 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_678 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i45 : (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_585 c0_level r1_depth r2_depth) (fun l0 => (False.elim (l0 (replay_677 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_651 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i50 i45 i51 i52)))) (fun t1 => t1))))

theorem propositional_449 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_679 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_186 c2_level r2_depth r2_kind r2_node r2_sign) ∨ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) := by
  exact (propositional_449 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_node % (2 : Int)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_680 (r2_sign : Int) : ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_450 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_681 (r2_sign : Int) : (((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))) ∨ (r2_sign ≤ (1 : Int))) := by
  exact (propositional_450 (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)))

abbrev shared_expr_Repair017_2 (r2_sign : Int) : Prop := ((¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))))
abbrev formula_591 (r2_sign : Int) : Prop := (shared_expr_Repair017_2 r2_sign)

theorem propositional_451 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_682 (r2_sign : Int) : (formula_591 r2_sign) := by
  exact (propositional_451 ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_683 (r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i60 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))))) : (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) := by
  exact (Or.elim (replay_682 r2_sign) (fun l0 => (False.elim (l0 i60))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i59))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_684 (r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i60 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))))) : (r2_sign ≤ (1 : Int)) := by
  exact (Or.elim (replay_681 r2_sign) (fun l0 => (False.elim ((replay_683 r2_sign i59 i60) l0))) (fun t0 => t0))

theorem propositional_452 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_685 (r2_sign : Int) : (((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))) ∨ (r2_sign ≥ (2 : Int))) := by
  exact (propositional_452 (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

abbrev shared_expr_Repair017_3 (r2_sign : Int) : Prop := ((¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))
abbrev formula_592 (r2_sign : Int) : Prop := (shared_expr_Repair017_3 r2_sign)

theorem propositional_453 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_686 (r2_sign : Int) : (formula_592 r2_sign) := by
  exact (propositional_453 ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))) ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_687 (r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_686 r2_sign) (fun l0 => (False.elim (l0 i61))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i59))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_688 (r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : (r2_sign ≥ (2 : Int)) := by
  exact (Or.elim (replay_685 r2_sign) (fun l0 => (False.elim ((replay_687 r2_sign i59 i61) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_689 (r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i60 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))))) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) : False := by
  exact (Or.elim (replay_680 r2_sign) (fun l0 => (False.elim (l0 (replay_684 r2_sign i59 i60)))) (fun t0 => (False.elim (t0 (replay_688 r2_sign i59 i61)))))

abbrev shared_expr_Repair017_4 (r2_sign : Int) : Prop := ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))))
abbrev formula_593 (r2_sign : Int) : Prop := (shared_expr_Repair017_4 r2_sign)

-- Checked replay of lemma.
theorem replay_690 (r2_sign : Int) : (formula_593 r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_689 r2_sign (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))))

abbrev shared_expr_Repair017_5 (h r2_depth r2_sign : Int) : Prop := ((¬ (formula_170 h r2_depth r2_sign)) ∨ (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) ∨ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))))
abbrev formula_594 (h r2_depth r2_sign : Int) : Prop := (shared_expr_Repair017_5 h r2_depth r2_sign)

theorem propositional_454 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_691 (h r2_depth r2_sign : Int) : (formula_594 h r2_depth r2_sign) := by
  exact (propositional_454 ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int)))))) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

theorem propositional_455 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p7))))) ∨ (¬ p13)) ∨ p13) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_692 (h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : ((formula_171 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ∨ (formula_170 h r2_depth r2_sign)) := by
  exact (propositional_455 (r2_mode ≤ (0 : Int)) (r2_mode ≥ (0 : Int)) (r2_level ≤ (0 : Int)) (r2_level ≥ (0 : Int)) (r2_group ≤ (0 : Int)) (r2_group ≥ (0 : Int)) (r2_depth ≥ (0 : Int)) (r2_node ≥ (0 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_depth ≤ (0 : Int)) (r2_node ≤ (0 : Int)) (formula_170 h r2_depth r2_sign))

theorem propositional_456 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7)))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_693 (c0_level r2_depth r2_kind r2_sign : Int) : ((formula_67 c0_level r2_depth r2_kind r2_sign) ∨ (r2_kind ≤ (1 : Int))) := by
  exact (propositional_456 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_694 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (r2_kind ≤ (1 : Int)) := by
  exact (Or.elim (replay_693 c0_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_676 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_695 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (r2_kind ≥ (2 : Int))) := by
  exact (Or.elim (replay_231 r2_kind) (fun l0 => (False.elim (l0 (replay_694 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_696 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i51 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (formula_159 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (Or.elim (replay_114 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_695 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i50 i51 i52) t0))))

abbrev shared_expr_Repair017_6 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (formula_561 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))))
abbrev formula_595 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_6 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)

theorem propositional_457 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ ((((¬ p5) ∨ (¬ p6)) ∧ ((((¬ p7) ∨ (¬ p8)) ∧ ((¬ p9) ∨ (¬ p10) ∨ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p11)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14))))))) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p17) ∨ (¬ p18)))))))) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ ((((¬ p19) ∨ (¬ p20)) ∧ (¬ p20)) ∨ ((¬ ((¬ p19) ∨ (¬ p20))) ∧ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ p13) ∨ (¬ p14)))))))))) ∨ p2) := by
  classical
  first | (by_cases case_p2 : p2 <;> simp [case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_697 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ∨ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) := by
  exact (propositional_457 (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int)) ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) ((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))

abbrev shared_expr_Repair017_7 (r1_group r1_mode r2_group r2_mode : Int) : Prop := ((((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))))) ∧ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))))
abbrev formula_596 (r1_group r1_mode r2_group r2_mode : Int) : Prop := (shared_expr_Repair017_7 r1_group r1_mode r2_group r2_mode)

abbrev shared_expr_Repair017_8 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int))))) ∧ (formula_596 r1_group r1_mode r2_group r2_mode)))
abbrev formula_597 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair017_8 r1_group r1_level r1_mode r2_group r2_level r2_mode)

abbrev shared_expr_Repair017_9 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))) ∨ ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))))
abbrev formula_598 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (shared_expr_Repair017_9 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)

abbrev shared_expr_Repair017_10 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ∧ (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) ∨ ((¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ∧ (formula_598 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)))
abbrev formula_599 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_10 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair017_11 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ∨ (¬ (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)) ∨ (¬ (formula_599 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)))
abbrev formula_600 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_11 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem propositional_458 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ p0) ∨ (¬ p1) ∨ (¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ ((¬ p2) ∨ (¬ p3) ∨ (((p4 ↔ p5) ∧ ((((¬ p6) ∨ (¬ p7)) ∧ (¬ p7)) ∨ ((¬ ((¬ p6) ∨ (¬ p7))) ∧ ((((¬ p8) ∨ (¬ p9)) ∧ (¬ p9)) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ (¬ p10)))))) ∨ ((¬ (p4 ↔ p5)) ∧ p4))))))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_698 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_600 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (propositional_458 ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (r2_kind ≤ (0 : Int)) (r2_kind ≥ (0 : Int)) (r1_mode ≥ (4 : Int)) (r2_mode ≥ (4 : Int)) ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)) ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair017_12 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ (¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))))) ∧ (((r1_level ≠ r2_level) ∧ (r1_level < r2_level)) ∨ ((¬ (r1_level ≠ r2_level)) ∧ (((r1_mode ≠ r2_mode) ∧ (r1_mode < r2_mode)) ∨ ((¬ (r1_mode ≠ r2_mode)) ∧ (r1_group < r2_group))))))
abbrev formula_601 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int))) ∨ (shared_expr_Repair017_12 r1_group r1_level r1_mode r2_group r2_level r2_mode))

abbrev shared_expr_Repair017_13 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := ((((r2_depth + (1 : Int)) = r1_depth) ∧ (((r2_node = (r1_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r1_node / (2 : Int)))) ∧ ((r1_node / (2 : Int)) < r2_node)))) ∨ ((¬ ((r2_depth + (1 : Int)) = r1_depth)) ∧ True))
abbrev formula_602 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_13 r1_depth r1_node r2_depth r2_node r2_sign)

abbrev shared_expr_Repair017_14 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((((r1_depth + (1 : Int)) = r2_depth) ∧ (((r1_node = (r2_node / (2 : Int))) ∧ (r1_sign = (1 : Int))) ∨ ((¬ (r1_node = (r2_node / (2 : Int)))) ∧ (r1_node < (r2_node / (2 : Int)))))) ∨ ((¬ ((r1_depth + (1 : Int)) = r2_depth)) ∧ (formula_602 r1_depth r1_node r2_depth r2_node r2_sign)))
abbrev formula_603 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_14 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair017_15 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((r1_depth = r2_depth) ∧ (((r1_node = r2_node) ∧ ((r1_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r1_node = r2_node)) ∧ (r1_node < r2_node)))) ∨ ((¬ (r1_depth = r2_depth)) ∧ (formula_603 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
abbrev formula_604 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_15 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair017_16 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((r1_kind = (2 : Int)) ∧ (False ∧ (r2_kind = (1 : Int)))) ∨ ((¬ (r1_kind = (2 : Int))) ∧ (((r2_kind = (2 : Int)) ∧ True) ∨ ((¬ (r2_kind = (2 : Int))) ∧ (formula_604 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))))
abbrev formula_605 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_16 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair017_17 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((r1_kind = (0 : Int)) ∧ (((r2_kind = (0 : Int)) ∧ (formula_601 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ (r2_kind = (0 : Int))) ∧ True))) ∨ ((¬ (r1_kind = (0 : Int))) ∧ (((r2_kind = (0 : Int)) ∧ False) ∨ ((¬ (r2_kind = (0 : Int))) ∧ (formula_605 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))))
abbrev formula_606 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_17 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair017_18 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (((r1_level = r2_level) ∧ (((r1_mode = r2_mode) ∧ (¬ (r2_group ≤ r1_group))) ∨ ((¬ (r1_mode = r2_mode)) ∧ (¬ (r2_mode ≤ r1_mode))))) ∨ ((¬ (r1_level = r2_level)) ∧ (¬ (r2_level ≤ r1_level)))))
abbrev formula_607 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Repair017_18 r1_group r1_level r1_mode r2_group r2_level r2_mode) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int))))

abbrev shared_expr_Repair017_19 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := ((¬ (r1_depth = ((-1 : Int) + r2_depth))) ∧ ((¬ (r2_depth = ((-1 : Int) + r1_depth))) ∨ (((r2_node = (r1_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r1_node / (2 : Int)))) ∧ (¬ (r2_node ≤ (r1_node / (2 : Int))))))))
abbrev shared_expr_Repair017_20 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((r1_depth = ((-1 : Int) + r2_depth)) ∧ (((r1_node = (r2_node / (2 : Int))) ∧ (r1_sign = (1 : Int))) ∨ ((¬ (r1_node = (r2_node / (2 : Int)))) ∧ (¬ ((r2_node / (2 : Int)) ≤ r1_node))))) ∨ (shared_expr_Repair017_19 r1_depth r1_node r2_depth r2_node r2_sign))
abbrev formula_608 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_20 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair017_21 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((r1_depth = r2_depth) ∧ (((r1_node = r2_node) ∧ ((r1_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r1_node = r2_node)) ∧ (¬ (r2_node ≤ r1_node))))) ∨ ((¬ (r1_depth = r2_depth)) ∧ (formula_608 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
abbrev formula_609 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_21 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair017_22 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((r1_kind = (0 : Int)) ∧ ((¬ (r2_kind = (0 : Int))) ∨ (formula_607 r1_group r1_level r1_mode r2_group r2_level r2_mode))) ∨ ((¬ (r1_kind = (0 : Int))) ∧ ((¬ (r2_kind = (0 : Int))) ∧ (¬ (r1_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_609 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))))
abbrev formula_610 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_22 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair017_23 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_610 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_611 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair017_23 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_459 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (False ∧ (p10 ∧ (¬ p11)))) ∨ ((¬ p9) ∧ ((p12 ∧ True) ∨ ((¬ p12) ∧ ((p13 ∧ ((p14 ∧ p15) ∨ ((¬ p14) ∧ p16))) ∨ ((¬ p13) ∧ ((p17 ∧ p18) ∨ ((¬ p17) ∧ ((p19 ∧ ((p20 ∧ p21) ∨ ((¬ p20) ∧ p22))) ∨ ((¬ p19) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ (¬ p9) ∧ (p12 ∨ ((p13 ∧ ((p14 ∧ p15) ∨ ((¬ p14) ∧ (¬ (¬ p16))))) ∨ ((¬ p13) ∧ ((p17 ∧ p18) ∨ ((¬ p17) ∧ ((¬ p19) ∨ ((p20 ∧ p21) ∨ ((¬ p20) ∧ (¬ (¬ p22)))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2466 (r1_mode r2_mode : Int) : (¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_2271 r1_mode) (normalization_534 r2_mode)))

theorem normalization_2467 (r1_level r2_level : Int) : (r1_level ≠ r2_level) ↔ (¬ (((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_2468 (r1_level r2_level : Int) : (r1_level < r2_level) ↔ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2469 (r1_mode r2_mode : Int) : (r1_mode ≠ r2_mode) ↔ (¬ (((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_2470 (r1_mode r2_mode : Int) : (r1_mode < r2_mode) ↔ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2471 (r1_group r2_group : Int) : (r1_group < r2_group) ↔ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair017_24 (r1_group r1_mode r2_group r2_mode : Int) : Prop := (((¬ (((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) ∧ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))))) ∧ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))))
theorem normalization_2472 (r1_group r1_mode r2_group r2_mode : Int) : (((r1_mode ≠ r2_mode) ∧ (r1_mode < r2_mode)) ∨ ((¬ (r1_mode ≠ r2_mode)) ∧ (r1_group < r2_group))) ↔ (shared_expr_Repair017_24 r1_group r1_mode r2_group r2_mode) := (or_congr (and_congr (normalization_2469 r1_mode r2_mode) (normalization_2470 r1_mode r2_mode)) (and_congr (not_congr (normalization_2469 r1_mode r2_mode)) (normalization_2471 r1_group r2_group)))

abbrev shared_expr_Repair017_25 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ (((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) ∧ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair017_24 r1_group r1_mode r2_group r2_mode)))
theorem normalization_2473 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (((r1_level ≠ r2_level) ∧ (r1_level < r2_level)) ∨ ((¬ (r1_level ≠ r2_level)) ∧ (((r1_mode ≠ r2_mode) ∧ (r1_mode < r2_mode)) ∨ ((¬ (r1_mode ≠ r2_mode)) ∧ (r1_group < r2_group))))) ↔ (shared_expr_Repair017_25 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2467 r1_level r2_level) (normalization_2468 r1_level r2_level)) (and_congr (not_congr (normalization_2467 r1_level r2_level)) (normalization_2472 r1_group r1_mode r2_group r2_mode)))

abbrev shared_expr_Repair017_26 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) ∧ (¬ ((r1_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair017_25 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
theorem normalization_2474 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_601 r1_group r1_level r1_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair017_26 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2466 r1_mode r2_mode) (normalization_2271 r1_mode)) (and_congr (not_congr (normalization_2466 r1_mode r2_mode)) (normalization_2473 r1_group r1_level r1_mode r2_group r2_level r2_mode)))

abbrev shared_expr_Repair017_27 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair017_26 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_2475 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : (((r2_kind = (0 : Int)) ∧ (formula_601 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ (r2_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Repair017_27 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode) := (or_congr (and_congr (normalization_133 r2_kind) (normalization_2474 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_133 r2_kind)) (normalization_305)))

theorem normalization_2476 (r2_kind : Int) : (False ∧ (r2_kind = (1 : Int))) ↔ (False ∧ (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int))))) := (and_congr (normalization_1253) (normalization_181 r2_kind))

theorem normalization_2477 (r1_depth r2_depth : Int) : (r1_depth = r2_depth) ↔ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2478 (r1_node r2_node : Int) : (r1_node = r2_node) ↔ (((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2479 (r1_sign : Int) : (r1_sign = (1 : Int)) ↔ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) := by
  omega

theorem normalization_2480 (r1_sign r2_sign : Int) : ((r1_sign = (1 : Int)) ∧ (r2_sign = (0 : Int))) ↔ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) := (and_congr (normalization_2479 r1_sign) (normalization_183 r2_sign))

theorem normalization_2481 (r1_node r2_node : Int) : (r1_node < r2_node) ↔ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair017_28 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∧ ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))))
abbrev shared_expr_Repair017_29 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((shared_expr_Repair017_28 r1_node r1_sign r2_node r2_sign) ∨ ((¬ (((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) ∧ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
theorem normalization_2482 (r1_node r1_sign r2_node r2_sign : Int) : (((r1_node = r2_node) ∧ ((r1_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r1_node = r2_node)) ∧ (r1_node < r2_node))) ↔ (shared_expr_Repair017_29 r1_node r1_sign r2_node r2_sign) := (or_congr (and_congr (normalization_2478 r1_node r2_node) (normalization_2480 r1_sign r2_sign)) (and_congr (not_congr (normalization_2478 r1_node r2_node)) (normalization_2481 r1_node r2_node)))

theorem normalization_2483 (r1_depth r2_depth : Int) : ((r1_depth + (1 : Int)) = r2_depth) ↔ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2484 (r1_node r2_node : Int) : (r1_node = (r2_node / (2 : Int))) ↔ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2485 (r1_node r2_node : Int) : (r1_node < (r2_node / (2 : Int))) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Repair017_30 (r1_node r2_node : Int) : Prop := ((¬ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) ∧ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair017_31 (r1_node r1_sign r2_node : Int) : Prop := ((((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∧ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair017_30 r1_node r2_node))
theorem normalization_2486 (r1_node r1_sign r2_node : Int) : (((r1_node = (r2_node / (2 : Int))) ∧ (r1_sign = (1 : Int))) ∨ ((¬ (r1_node = (r2_node / (2 : Int)))) ∧ (r1_node < (r2_node / (2 : Int))))) ↔ (shared_expr_Repair017_31 r1_node r1_sign r2_node) := (or_congr (and_congr (normalization_2484 r1_node r2_node) (normalization_2479 r1_sign)) (and_congr (not_congr (normalization_2484 r1_node r2_node)) (normalization_2485 r1_node r2_node)))

theorem normalization_2487 (r1_depth r2_depth : Int) : ((r2_depth + (1 : Int)) = r1_depth) ↔ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_2488 (r1_node r2_node : Int) : (r2_node = (r1_node / (2 : Int))) ↔ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2489 (r1_node r2_node : Int) : ((r1_node / (2 : Int)) < r2_node) ↔ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair017_32 (r1_node r2_node : Int) : Prop := ((¬ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair017_33 (r1_node r2_node r2_sign : Int) : Prop := ((((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair017_32 r1_node r2_node))
theorem normalization_2490 (r1_node r2_node r2_sign : Int) : (((r2_node = (r1_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r1_node / (2 : Int)))) ∧ ((r1_node / (2 : Int)) < r2_node))) ↔ (shared_expr_Repair017_33 r1_node r2_node r2_sign) := (or_congr (and_congr (normalization_2488 r1_node r2_node) (normalization_183 r2_sign)) (and_congr (not_congr (normalization_2488 r1_node r2_node)) (normalization_2489 r1_node r2_node)))

abbrev shared_expr_Repair017_34 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∧ (shared_expr_Repair017_33 r1_node r2_node r2_sign)) ∨ ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_2491 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : (formula_602 r1_depth r1_node r2_depth r2_node r2_sign) ↔ (shared_expr_Repair017_34 r1_depth r1_node r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2487 r1_depth r2_depth) (normalization_2490 r1_node r2_node r2_sign)) (and_congr (not_congr (normalization_2487 r1_depth r2_depth)) (normalization_305)))

abbrev shared_expr_Repair017_35 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair017_31 r1_node r1_sign r2_node)) ∨ ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair017_34 r1_depth r1_node r2_depth r2_node r2_sign)))
theorem normalization_2492 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_603 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair017_35 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2483 r1_depth r2_depth) (normalization_2486 r1_node r1_sign r2_node)) (and_congr (not_congr (normalization_2483 r1_depth r2_depth)) (normalization_2491 r1_depth r1_node r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair017_36 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair017_29 r1_node r1_sign r2_node r2_sign)) ∨ ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair017_35 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2493 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_604 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair017_36 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2477 r1_depth r2_depth) (normalization_2482 r1_node r1_sign r2_node r2_sign)) (and_congr (not_congr (normalization_2477 r1_depth r2_depth)) (normalization_2492 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair017_37 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∧ True) ∨ ((¬ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair017_36 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2494 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (((r2_kind = (2 : Int)) ∧ True) ∨ ((¬ (r2_kind = (2 : Int))) ∧ (formula_604 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))) ↔ (shared_expr_Repair017_37 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (or_congr (and_congr (normalization_201 r2_kind) (normalization_305)) (and_congr (not_congr (normalization_201 r2_kind)) (normalization_2493 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair017_38 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∧ (False ∧ (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))))) ∨ ((¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair017_37 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_2495 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_605 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Repair017_38 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (or_congr (and_congr (normalization_2284 r1_kind) (normalization_2476 r2_kind)) (and_congr (not_congr (normalization_2284 r1_kind)) (normalization_2494 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair017_39 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair017_38 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_2496 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (((r2_kind = (0 : Int)) ∧ False) ∨ ((¬ (r2_kind = (0 : Int))) ∧ (formula_605 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign))) ↔ (shared_expr_Repair017_39 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (or_congr (and_congr (normalization_133 r2_kind) (normalization_1253)) (and_congr (not_congr (normalization_133 r2_kind)) (normalization_2495 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair017_40 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair017_27 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair017_39 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_2497 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair017_40 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_2270 r1_kind) (normalization_2475 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) (and_congr (not_congr (normalization_2270 r1_kind)) (normalization_2496 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

theorem normalization_2498 (r2_kind : Int) : (¬ (r2_kind = (0 : Int))) ↔ (¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) := (not_congr (normalization_133 r2_kind))

theorem normalization_2499 (r1_mode r2_mode : Int) : ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ↔ ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))) := (iff_congr (normalization_2271 r1_mode) (normalization_534 r2_mode))

theorem normalization_2500 (r1_level r2_level : Int) : (r1_level = r2_level) ↔ (((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2501 (r1_mode r2_mode : Int) : (r1_mode = r2_mode) ↔ (((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2502 (r1_group r2_group : Int) : (r2_group ≤ r1_group) ↔ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2503 (r1_group r2_group : Int) : (¬ (r2_group ≤ r1_group)) ↔ (¬ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_2502 r1_group r2_group))

theorem normalization_2504 (r1_mode r2_mode : Int) : (r2_mode ≤ r1_mode) ↔ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2505 (r1_mode r2_mode : Int) : (¬ (r2_mode ≤ r1_mode)) ↔ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_2504 r1_mode r2_mode))

abbrev shared_expr_Repair017_41 (r1_group r1_mode r2_group r2_mode : Int) : Prop := (((((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))))
theorem normalization_2506 (r1_group r1_mode r2_group r2_mode : Int) : (((r1_mode = r2_mode) ∧ (¬ (r2_group ≤ r1_group))) ∨ ((¬ (r1_mode = r2_mode)) ∧ (¬ (r2_mode ≤ r1_mode)))) ↔ (shared_expr_Repair017_41 r1_group r1_mode r2_group r2_mode) := (or_congr (and_congr (normalization_2501 r1_mode r2_mode) (normalization_2503 r1_group r2_group)) (and_congr (not_congr (normalization_2501 r1_mode r2_mode)) (normalization_2505 r1_mode r2_mode)))

theorem normalization_2507 (r1_level r2_level : Int) : (r2_level ≤ r1_level) ↔ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2508 (r1_level r2_level : Int) : (¬ (r2_level ≤ r1_level)) ↔ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2507 r1_level r2_level))

abbrev shared_expr_Repair017_42 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair017_41 r1_group r1_mode r2_group r2_mode)) ∨ ((¬ (((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))))
theorem normalization_2509 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (((r1_level = r2_level) ∧ (((r1_mode = r2_mode) ∧ (¬ (r2_group ≤ r1_group))) ∨ ((¬ (r1_mode = r2_mode)) ∧ (¬ (r2_mode ≤ r1_mode))))) ∨ ((¬ (r1_level = r2_level)) ∧ (¬ (r2_level ≤ r1_level)))) ↔ (shared_expr_Repair017_42 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2500 r1_level r2_level) (normalization_2506 r1_group r1_mode r2_group r2_mode)) (and_congr (not_congr (normalization_2500 r1_level r2_level)) (normalization_2508 r1_level r2_level)))

abbrev shared_expr_Repair017_43 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair017_42 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((¬ ((r1_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) ∧ (¬ ((r1_mode) ≤ (3 : Int)))))
theorem normalization_2510 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_607 r1_group r1_level r1_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair017_43 r1_group r1_level r1_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_2499 r1_mode r2_mode) (normalization_2509 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_2499 r1_mode r2_mode)) (normalization_2271 r1_mode)))

theorem normalization_2511 (r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : ((¬ (r2_kind = (0 : Int))) ∨ (formula_607 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ↔ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair017_43 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := (or_congr (normalization_2498 r2_kind) (normalization_2510 r1_group r1_level r1_mode r2_group r2_level r2_mode))

theorem normalization_2512 (r1_kind : Int) : (¬ (r1_kind = (2 : Int))) ↔ (¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) := (not_congr (normalization_2284 r1_kind))

theorem normalization_2513 (r1_node r2_node : Int) : (r2_node ≤ r1_node) ↔ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2514 (r1_node r2_node : Int) : (¬ (r2_node ≤ r1_node)) ↔ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2513 r1_node r2_node))

abbrev shared_expr_Repair017_44 (r1_node r1_sign r2_node r2_sign : Int) : Prop := ((shared_expr_Repair017_28 r1_node r1_sign r2_node r2_sign) ∨ ((¬ (((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))))
theorem normalization_2515 (r1_node r1_sign r2_node r2_sign : Int) : (((r1_node = r2_node) ∧ ((r1_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r1_node = r2_node)) ∧ (¬ (r2_node ≤ r1_node)))) ↔ (shared_expr_Repair017_44 r1_node r1_sign r2_node r2_sign) := (or_congr (and_congr (normalization_2478 r1_node r2_node) (normalization_2480 r1_sign r2_sign)) (and_congr (not_congr (normalization_2478 r1_node r2_node)) (normalization_2514 r1_node r2_node)))

theorem normalization_2516 (r1_depth r2_depth : Int) : (r1_depth = ((-1 : Int) + r2_depth)) ↔ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2517 (r1_node r2_node : Int) : ((r2_node / (2 : Int)) ≤ r1_node) ↔ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2518 (r1_node r2_node : Int) : (¬ ((r2_node / (2 : Int)) ≤ r1_node)) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := (not_congr (normalization_2517 r1_node r2_node))

theorem normalization_2519 (r1_node r1_sign r2_node : Int) : (((r1_node = (r2_node / (2 : Int))) ∧ (r1_sign = (1 : Int))) ∨ ((¬ (r1_node = (r2_node / (2 : Int)))) ∧ (¬ ((r2_node / (2 : Int)) ≤ r1_node)))) ↔ (shared_expr_Repair017_31 r1_node r1_sign r2_node) := (or_congr (and_congr (normalization_2484 r1_node r2_node) (normalization_2479 r1_sign)) (and_congr (not_congr (normalization_2484 r1_node r2_node)) (normalization_2518 r1_node r2_node)))

theorem normalization_2520 (r1_depth r2_depth : Int) : (r2_depth = ((-1 : Int) + r1_depth)) ↔ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_2521 (r1_depth r2_depth : Int) : (¬ (r2_depth = ((-1 : Int) + r1_depth))) ↔ (¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) := (not_congr (normalization_2520 r1_depth r2_depth))

theorem normalization_2522 (r1_node r2_node : Int) : (r2_node ≤ (r1_node / (2 : Int))) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2523 (r1_node r2_node : Int) : (¬ (r2_node ≤ (r1_node / (2 : Int)))) ↔ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2522 r1_node r2_node))

abbrev shared_expr_Repair017_45 (r1_node r2_node : Int) : Prop := ((¬ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair017_46 (r1_node r2_node r2_sign : Int) : Prop := ((((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair017_45 r1_node r2_node))
theorem normalization_2524 (r1_node r2_node r2_sign : Int) : (((r2_node = (r1_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r1_node / (2 : Int)))) ∧ (¬ (r2_node ≤ (r1_node / (2 : Int)))))) ↔ (shared_expr_Repair017_46 r1_node r2_node r2_sign) := (or_congr (and_congr (normalization_2488 r1_node r2_node) (normalization_183 r2_sign)) (and_congr (not_congr (normalization_2488 r1_node r2_node)) (normalization_2523 r1_node r2_node)))

theorem normalization_2525 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : ((¬ (r2_depth = ((-1 : Int) + r1_depth))) ∨ (((r2_node = (r1_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r1_node / (2 : Int)))) ∧ (¬ (r2_node ≤ (r1_node / (2 : Int))))))) ↔ ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair017_46 r1_node r2_node r2_sign)) := (or_congr (normalization_2521 r1_depth r2_depth) (normalization_2524 r1_node r2_node r2_sign))

abbrev shared_expr_Repair017_47 (r1_depth r1_node r2_depth r2_node r2_sign : Int) : Prop := ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair017_46 r1_node r2_node r2_sign)))
abbrev shared_expr_Repair017_48 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair017_31 r1_node r1_sign r2_node)) ∨ (shared_expr_Repair017_47 r1_depth r1_node r2_depth r2_node r2_sign))
theorem normalization_2526 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_608 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair017_48 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2516 r1_depth r2_depth) (normalization_2519 r1_node r1_sign r2_node)) (and_congr (not_congr (normalization_2516 r1_depth r2_depth)) (normalization_2525 r1_depth r1_node r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair017_49 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair017_44 r1_node r1_sign r2_node r2_sign)) ∨ ((¬ (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair017_48 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2527 (r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_609 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair017_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_2477 r1_depth r2_depth) (normalization_2515 r1_node r1_sign r2_node r2_sign)) (and_congr (not_congr (normalization_2477 r1_depth r2_depth)) (normalization_2526 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))

theorem normalization_2528 (r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((r2_kind = (2 : Int)) ∨ (formula_609 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) ↔ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair017_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)) := (or_congr (normalization_201 r2_kind) (normalization_2527 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))

abbrev shared_expr_Repair017_50 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ∧ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair017_49 r1_depth r1_node r1_sign r2_depth r2_node r2_sign)))
theorem normalization_2529 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (r2_kind = (0 : Int))) ∧ (¬ (r1_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_609 r1_depth r1_node r1_sign r2_depth r2_node r2_sign))) ↔ (shared_expr_Repair017_50 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := (and_congr (normalization_2498 r2_kind) (and_congr (normalization_2512 r1_kind) (normalization_2528 r1_depth r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair017_51 (r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair017_43 r1_group r1_level r1_mode r2_group r2_level r2_mode)))
abbrev shared_expr_Repair017_52 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair017_51 r1_group r1_kind r1_level r1_mode r2_group r2_kind r2_level r2_mode) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair017_50 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_2530 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_610 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair017_52 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_2270 r1_kind) (normalization_2511 r1_group r1_level r1_mode r2_group r2_kind r2_level r2_mode)) (and_congr (not_congr (normalization_2270 r1_kind)) (normalization_2529 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair017_53 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair017_40 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair017_52 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_2531 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_611 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair017_53 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_2497 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_2530 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_699 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_611 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_459 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ((r1_mode) ≤ (3 : Int)) ((r2_mode) ≤ (3 : Int)) (((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ((r1_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) (((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((r1_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ((r2_kind) ≤ (1 : Int)) ((r2_kind) ≤ (0 : Int)) (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (((r1_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ((((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int)))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) ((r1_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) (((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair017_31 r1_node r1_sign r2_node) ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) (((r1_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2531 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

end H4Formal.Generated.Repair
