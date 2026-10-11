import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair013

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of mp.
theorem replay_466 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i27 : ((formula_407 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) : (formula_386 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact Iff.mp (replay_465 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_313 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i27)

-- Checked replay of unit-resolution.
theorem replay_467 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i27 : ((formula_407 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) : (((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) ∨ (formula_359 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign r0_group r0_level r0_mode)) := by
  exact (Or.elim (replay_298 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl (Or.inl l100))) (fun t100 => (Or.inl (Or.inr t100))))) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr l1)) (fun t1 => (False.elim (t1 (replay_466 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i27)))))))

theorem propositional_352 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_468 (r0_kind : Int) : ((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∨ (¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) := by
  exact (propositional_352 (r0_kind ≤ (0 : Int)) (r0_kind ≥ (0 : Int)))

abbrev shared_expr_Repair014_0 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((r0_mode ≥ (6 : Int)) ∨ (¬ (r0_node ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r0_group ≤ (2 : Int))) ∨ (¬ (r0_group ≥ (2 : Int))))))) ∨ (¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_depth ≤ (0 : Int))) ∨ (¬ (r0_depth ≥ (0 : Int))) ∨ (¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))) ∨ (¬ (r0_node ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int))) ∨ (¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))) ∨ (¬ (r0_level ≥ (1 : Int))))
abbrev formula_500 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_0 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem propositional_353 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p15)) ∨ p14) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_469 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (r0_kind ≥ (0 : Int))) := by
  exact (propositional_353 (r0_mode ≥ (6 : Int)) (r0_node ≥ (0 : Int)) (r0_group ≤ (1 : Int)) (r0_group ≥ (1 : Int)) (r0_group ≤ (2 : Int)) (r0_group ≥ (2 : Int)) (r0_mode ≥ (0 : Int)) (r0_depth ≤ (0 : Int)) (r0_depth ≥ (0 : Int)) (r0_sign ≤ (0 : Int)) (r0_sign ≥ (0 : Int)) (r0_node ≤ (0 : Int)) ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int)) (r0_kind ≤ (0 : Int)) (r0_kind ≥ (0 : Int)) (r0_level ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_470 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i28 : (¬ (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : (r0_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_469 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (False.elim (i28 l0))) (fun t0 => t0))

theorem propositional_354 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p15)) ∨ p13) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_471 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (r0_kind ≤ (0 : Int))) := by
  exact (propositional_354 (r0_mode ≥ (6 : Int)) (r0_node ≥ (0 : Int)) (r0_group ≤ (1 : Int)) (r0_group ≥ (1 : Int)) (r0_group ≤ (2 : Int)) (r0_group ≥ (2 : Int)) (r0_mode ≥ (0 : Int)) (r0_depth ≤ (0 : Int)) (r0_depth ≥ (0 : Int)) (r0_sign ≤ (0 : Int)) (r0_sign ≥ (0 : Int)) (r0_node ≤ (0 : Int)) ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int)) (r0_kind ≤ (0 : Int)) (r0_kind ≥ (0 : Int)) (r0_level ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_472 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i28 : (¬ (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : (r0_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_471 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (False.elim (i28 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_473 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i28 : (¬ (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) (i29 : ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) : False := by
  exact (Or.elim (replay_468 r0_kind) (fun l0 => (False.elim (l0 i29))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_472 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i28)))) (fun t1 => (False.elim (t1 (replay_470 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i28)))))))

-- Checked replay of lemma.
theorem replay_474 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_473 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

abbrev shared_expr_Repair014_1 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((r0_kind = (0 : Int)) ∧ (r0_mode ≥ (0 : Int)) ∧ (r0_mode < (6 : Int)) ∧ (r0_level ≥ (1 : Int)) ∧ (r0_level ≤ h) ∧ ((r0_group = (1 : Int)) ∨ (r0_group = (2 : Int))) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int)))
abbrev formula_501 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_1 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair014_2 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((r0_kind = (0 : Int)) ∧ (r0_mode ≥ (0 : Int)) ∧ (¬ ((6 : Int) ≤ r0_mode)) ∧ (r0_level ≥ (1 : Int)) ∧ (r0_level ≤ h) ∧ ((r0_group = (1 : Int)) ∨ (r0_group = (2 : Int))) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int)))
abbrev formula_502 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_2 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_355 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : ((p0 ∧ (¬ p1) ∧ p2 ∧ (¬ p3) ∧ (¬ p4) ∧ p5 ∧ p6 ∧ p7 ∧ p8) ↔ (p0 ∧ (¬ p1) ∧ (¬ (¬ p2)) ∧ (¬ p3) ∧ (¬ p4) ∧ p5 ∧ p6 ∧ p7 ∧ p8)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2190 (r0_mode : Int) : (r0_mode < (6 : Int)) ↔ ((r0_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_2191 (r0_level : Int) : (r0_level ≥ (1 : Int)) ↔ (¬ ((r0_level) ≤ (0 : Int))) := by
  omega

theorem normalization_2192 (h r0_level : Int) : (r0_level ≤ h) ↔ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2193 (r0_group : Int) : (r0_group = (2 : Int)) ↔ (((r0_group) ≤ (2 : Int)) ∧ (¬ ((r0_group) ≤ (1 : Int)))) := by
  omega

theorem normalization_2194 (r0_group : Int) : ((r0_group = (1 : Int)) ∨ (r0_group = (2 : Int))) ↔ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∨ (((r0_group) ≤ (2 : Int)) ∧ (¬ ((r0_group) ≤ (1 : Int))))) := (or_congr (normalization_1445 r0_group) (normalization_2193 r0_group))

theorem normalization_2195 (r0_depth : Int) : (r0_depth = (0 : Int)) ↔ (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2196 (r0_node : Int) : (r0_node = (0 : Int)) ↔ (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int)))) := by
  omega

abbrev shared_expr_Repair014_3 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ (¬ ((r0_mode) ≤ (-1 : Int))) ∧ ((r0_mode) ≤ (5 : Int)) ∧ (¬ ((r0_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∨ (((r0_group) ≤ (2 : Int)) ∧ (¬ ((r0_group) ≤ (1 : Int))))) ∧ (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) ∧ (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int)))) ∧ (((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))))
theorem normalization_2197 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_501 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_3 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (and_congr (normalization_1438 r0_kind) (and_congr (normalization_1748 r0_mode) (and_congr (normalization_2190 r0_mode) (and_congr (normalization_2191 r0_level) (and_congr (normalization_2192 h r0_level) (and_congr (normalization_2194 r0_group) (and_congr (normalization_2195 r0_depth) (and_congr (normalization_2196 r0_node) (normalization_1488 r0_sign)))))))))

theorem normalization_2198 (r0_mode : Int) : ((6 : Int) ≤ r0_mode) ↔ (¬ ((r0_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2199 (r0_mode : Int) : (¬ ((6 : Int) ≤ r0_mode)) ↔ (¬ (¬ ((r0_mode) ≤ (5 : Int)))) := (not_congr (normalization_2198 r0_mode))

abbrev shared_expr_Repair014_4 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ (¬ ((r0_mode) ≤ (-1 : Int))) ∧ (¬ (¬ ((r0_mode) ≤ (5 : Int)))) ∧ (¬ ((r0_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) ∧ ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∨ (((r0_group) ≤ (2 : Int)) ∧ (¬ ((r0_group) ≤ (1 : Int))))) ∧ (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) ∧ (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int)))) ∧ (((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))))
theorem normalization_2200 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_502 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (and_congr (normalization_1438 r0_kind) (and_congr (normalization_1748 r0_mode) (and_congr (normalization_2199 r0_mode) (and_congr (normalization_2191 r0_level) (and_congr (normalization_2192 h r0_level) (and_congr (normalization_2194 r0_group) (and_congr (normalization_2195 r0_depth) (and_congr (normalization_2196 r0_node) (normalization_1488 r0_sign)))))))))

theorem normalization_2201 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_501 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_502 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_3 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2197 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2200 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_475 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_501 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_502 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_355 (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ((r0_mode) ≤ (-1 : Int)) ((r0_mode) ≤ (5 : Int)) ((r0_level) ≤ (0 : Int)) ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((((r0_group) ≤ (1 : Int)) ∧ (¬ ((r0_group) ≤ (0 : Int)))) ∨ (((r0_group) ≤ (2 : Int)) ∧ (¬ ((r0_group) ≤ (1 : Int))))) (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int)))) (((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2201 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

abbrev shared_expr_Repair014_5 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((r0_kind = (1 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth ≥ (0 : Int)) ∧ (r0_depth ≤ h) ∧ (r0_node ≥ (0 : Int)) ∧ ((r0_depth = (0 : Int)) → (r0_node = (0 : Int))) ∧ (((r0_depth = h) ∧ (r0_sign = (2 : Int))) ∨ ((¬ (r0_depth = h)) ∧ ((r0_sign = (0 : Int)) ∨ (r0_sign = (1 : Int))))))
abbrev formula_503 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_5 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair014_6 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((r0_kind = (1 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth ≥ (0 : Int)) ∧ (r0_depth ≤ h) ∧ (r0_node ≥ (0 : Int)) ∧ ((¬ (r0_depth = (0 : Int))) ∨ (r0_node = (0 : Int))) ∧ (((r0_depth = h) ∧ (r0_sign = (2 : Int))) ∨ ((¬ (r0_depth = h)) ∧ ((r0_sign = (0 : Int)) ∨ (r0_sign = (1 : Int))))))
abbrev formula_504 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_6 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_356 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ (¬ p5) ∧ (¬ p6) ∧ (p7 → p8) ∧ p9) ↔ (p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ (¬ p5) ∧ (¬ p6) ∧ ((¬ p7) ∨ p8) ∧ p9)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2202 (r0_level : Int) : (r0_level = (0 : Int)) ↔ (((r0_level) ≤ (0 : Int)) ∧ (¬ ((r0_level) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2203 (r0_group : Int) : (r0_group = (0 : Int)) ↔ (((r0_group) ≤ (0 : Int)) ∧ (¬ ((r0_group) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2204 (r0_depth : Int) : (r0_depth ≥ (0 : Int)) ↔ (¬ ((r0_depth) ≤ (-1 : Int))) := by
  omega

theorem normalization_2205 (h r0_depth : Int) : (r0_depth ≤ h) ↔ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2206 (r0_node : Int) : (r0_node ≥ (0 : Int)) ↔ (¬ ((r0_node) ≤ (-1 : Int))) := by
  omega

theorem normalization_2207 (r0_depth r0_node : Int) : ((r0_depth = (0 : Int)) → (r0_node = (0 : Int))) ↔ ((((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) → (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int))))) := (imp_congr (normalization_2195 r0_depth) (normalization_2196 r0_node))

theorem normalization_2208 (r0_sign : Int) : ((r0_sign = (0 : Int)) ∨ (r0_sign = (1 : Int))) ↔ ((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int))))) := (or_congr (normalization_1488 r0_sign) (normalization_1497 r0_sign))

abbrev shared_expr_Repair014_7 (h r0_depth r0_sign : Int) : Prop := ((¬ ((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int)))) ∧ ((((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair014_8 (h r0_depth r0_sign : Int) : Prop := ((((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∧ (((r0_sign) ≤ (2 : Int)) ∧ (¬ ((r0_sign) ≤ (1 : Int))))) ∨ (shared_expr_Repair014_7 h r0_depth r0_sign))
theorem normalization_2209 (h r0_depth r0_sign : Int) : (((r0_depth = h) ∧ (r0_sign = (2 : Int))) ∨ ((¬ (r0_depth = h)) ∧ ((r0_sign = (0 : Int)) ∨ (r0_sign = (1 : Int))))) ↔ (shared_expr_Repair014_8 h r0_depth r0_sign) := (or_congr (and_congr (normalization_1533 h r0_depth) (normalization_1489 r0_sign)) (and_congr (not_congr (normalization_1533 h r0_depth)) (normalization_2208 r0_sign)))

abbrev shared_expr_Repair014_9 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (((r0_level) ≤ (0 : Int)) ∧ (¬ ((r0_level) ≤ (-1 : Int)))) ∧ (((r0_group) ≤ (0 : Int)) ∧ (¬ ((r0_group) ≤ (-1 : Int)))) ∧ (¬ ((r0_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ (¬ ((r0_node) ≤ (-1 : Int))) ∧ ((((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) → (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair014_8 h r0_depth r0_sign))
theorem normalization_2210 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_503 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_9 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (and_congr (normalization_1486 r0_kind) (and_congr (normalization_1444 r0_mode) (and_congr (normalization_2202 r0_level) (and_congr (normalization_2203 r0_group) (and_congr (normalization_2204 r0_depth) (and_congr (normalization_2205 h r0_depth) (and_congr (normalization_2206 r0_node) (and_congr (normalization_2207 r0_depth r0_node) (normalization_2209 h r0_depth r0_sign)))))))))

theorem normalization_2211 (r0_depth : Int) : (¬ (r0_depth = (0 : Int))) ↔ (¬ (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int))))) := (not_congr (normalization_2195 r0_depth))

theorem normalization_2212 (r0_depth r0_node : Int) : ((¬ (r0_depth = (0 : Int))) ∨ (r0_node = (0 : Int))) ↔ ((¬ (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int))))) ∨ (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int))))) := (or_congr (normalization_2211 r0_depth) (normalization_2196 r0_node))

abbrev shared_expr_Repair014_10 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) ∧ (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (((r0_level) ≤ (0 : Int)) ∧ (¬ ((r0_level) ≤ (-1 : Int)))) ∧ (((r0_group) ≤ (0 : Int)) ∧ (¬ ((r0_group) ≤ (-1 : Int)))) ∧ (¬ ((r0_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))) ∧ (¬ ((r0_node) ≤ (-1 : Int))) ∧ ((¬ (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int))))) ∨ (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair014_8 h r0_depth r0_sign))
theorem normalization_2213 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_504 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (and_congr (normalization_1486 r0_kind) (and_congr (normalization_1444 r0_mode) (and_congr (normalization_2202 r0_level) (and_congr (normalization_2203 r0_group) (and_congr (normalization_2204 r0_depth) (and_congr (normalization_2205 h r0_depth) (and_congr (normalization_2206 r0_node) (and_congr (normalization_2212 r0_depth r0_node) (normalization_2209 h r0_depth r0_sign)))))))))

theorem normalization_2214 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_503 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_504 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_9 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2210 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2213 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_476 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_503 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_504 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_356 (((r0_kind) ≤ (1 : Int)) ∧ (¬ ((r0_kind) ≤ (0 : Int)))) (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) (((r0_level) ≤ (0 : Int)) ∧ (¬ ((r0_level) ≤ (-1 : Int)))) (((r0_group) ≤ (0 : Int)) ∧ (¬ ((r0_group) ≤ (-1 : Int)))) ((r0_depth) ≤ (-1 : Int)) ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)) ((r0_node) ≤ (-1 : Int)) (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int)))) (shared_expr_Repair014_8 h r0_depth r0_sign))
  have hn := ht
  exact Iff.mpr (normalization_2214 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

abbrev shared_expr_Repair014_11 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((formula_501 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (formula_503 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ ((r0_kind = (2 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int))))
abbrev formula_505 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_11 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair014_12 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((formula_502 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (formula_504 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ ((r0_kind = (2 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int))))
abbrev formula_506 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_12 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_357 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ p1) ∧ (p2 ↔ p3)) → ((p0 ∨ p2 ∨ p4) ↔ (p1 ∨ p3 ∨ p4))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair014_13 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ∧ (((r0_mode) ≤ (0 : Int)) ∧ (¬ ((r0_mode) ≤ (-1 : Int)))) ∧ (((r0_level) ≤ (0 : Int)) ∧ (¬ ((r0_level) ≤ (-1 : Int)))) ∧ (((r0_group) ≤ (0 : Int)) ∧ (¬ ((r0_group) ≤ (-1 : Int)))) ∧ (((r0_depth) ≤ (0 : Int)) ∧ (¬ ((r0_depth) ≤ (-1 : Int)))) ∧ (((r0_node) ≤ (0 : Int)) ∧ (¬ ((r0_node) ≤ (-1 : Int)))) ∧ (((r0_sign) ≤ (0 : Int)) ∧ (¬ ((r0_sign) ≤ (-1 : Int)))))
theorem normalization_2215 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((r0_kind = (2 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int))) ↔ (shared_expr_Repair014_13 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (and_congr (normalization_1506 r0_kind) (and_congr (normalization_1444 r0_mode) (and_congr (normalization_2202 r0_level) (and_congr (normalization_2203 r0_group) (and_congr (normalization_2195 r0_depth) (and_congr (normalization_2196 r0_node) (normalization_1488 r0_sign)))))))

abbrev shared_expr_Repair014_14 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((shared_expr_Repair014_3 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (shared_expr_Repair014_9 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (shared_expr_Repair014_13 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
theorem normalization_2216 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_14 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2197 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (or_congr (normalization_2210 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2215 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)))

abbrev shared_expr_Repair014_15 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (shared_expr_Repair014_13 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
theorem normalization_2217 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_506 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_15 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2200 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (or_congr (normalization_2213 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2215 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)))

theorem normalization_2218 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_506 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_14 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_15 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2216 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2217 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of monotonicity.
theorem replay_477 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_506 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_357 (shared_expr_Repair014_3 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_9 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_13 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
  have n0 : ((shared_expr_Repair014_3 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
    exact Iff.mp (normalization_2201 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_475 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)
  have n1 : ((shared_expr_Repair014_9 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
    exact Iff.mp (normalization_2214 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_476 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2218 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

abbrev shared_expr_Repair014_16 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (((r0_kind = (2 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int))) ∨ (formula_502 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (formula_504 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
abbrev formula_507 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_16 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_358 (p0 p1 p2 : Prop) : ((p0 ∨ p1 ∨ p2) ↔ (p2 ∨ p0 ∨ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair014_17 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((shared_expr_Repair014_13 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
theorem normalization_2219 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2215 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (or_congr (normalization_2200 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2213 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)))

theorem normalization_2220 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_506 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_15 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2217 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2219 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_478 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_506 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_358 (shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_13 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
  have hn := ht
  exact Iff.mpr (normalization_2220 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

theorem normalized_359 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2221 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_14 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2216 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2219 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of trans.
theorem replay_479 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_359 (shared_expr_Repair014_14 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_15 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
  have n0 : ((shared_expr_Repair014_14 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_15 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
    exact Iff.mp (normalization_2218 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_477 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)
  have n1 : ((shared_expr_Repair014_15 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
    exact Iff.mp (normalization_2220 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_478 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2221 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

-- Checked replay of mp.
theorem replay_480 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) : (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact Iff.mp (replay_479 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) i30

theorem normalized_360 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2222 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2219 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2219 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_481 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_360 (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
  have hn := ht
  exact Iff.mpr (normalization_2222 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

-- Checked replay of mp.
theorem replay_482 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) : (formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact Iff.mp (replay_481 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_480 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i30)

abbrev shared_expr_Repair014_18 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((r0_kind = (0 : Int)) ∧ (r0_mode ≥ (0 : Int)) ∧ (¬ (r0_mode ≥ (6 : Int))) ∧ (r0_level ≥ (1 : Int)) ∧ ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int)) ∧ ((r0_group = (1 : Int)) ∨ (r0_group = (2 : Int))) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int)))
abbrev formula_508 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_18 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair014_19 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((r0_kind = (1 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int)) ∧ (r0_node ≥ (0 : Int)) ∧ ((¬ (r0_depth = (0 : Int))) ∨ (r0_node = (0 : Int))) ∧ (((r0_depth = h) ∧ (r0_sign = (2 : Int))) ∨ ((¬ (r0_depth = h)) ∧ ((r0_sign = (0 : Int)) ∨ (r0_sign = (1 : Int))))))
abbrev formula_509 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_19 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair014_20 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (((r0_kind = (2 : Int)) ∧ (r0_mode = (0 : Int)) ∧ (r0_level = (0 : Int)) ∧ (r0_group = (0 : Int)) ∧ (r0_depth = (0 : Int)) ∧ (r0_node = (0 : Int)) ∧ (r0_sign = (0 : Int))) ∨ (formula_508 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (formula_509 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
abbrev formula_510 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_20 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_361 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2223 (r0_mode : Int) : (r0_mode ≥ (6 : Int)) ↔ (¬ ((r0_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2224 (r0_mode : Int) : (¬ (r0_mode ≥ (6 : Int))) ↔ (¬ (¬ ((r0_mode) ≤ (5 : Int)))) := (not_congr (normalization_2223 r0_mode))

theorem normalization_2225 (h r0_level : Int) : ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int)) ↔ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2226 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_508 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_4 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (and_congr (normalization_1438 r0_kind) (and_congr (normalization_1748 r0_mode) (and_congr (normalization_2224 r0_mode) (and_congr (normalization_2191 r0_level) (and_congr (normalization_2225 h r0_level) (and_congr (normalization_2194 r0_group) (and_congr (normalization_2195 r0_depth) (and_congr (normalization_2196 r0_node) (normalization_1488 r0_sign)))))))))

theorem normalization_2227 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_509 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_10 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (and_congr (normalization_1486 r0_kind) (and_congr (normalization_1444 r0_mode) (and_congr (normalization_2202 r0_level) (and_congr (normalization_2203 r0_group) (and_congr (normalization_2204 r0_depth) (and_congr (normalization_2049 h r0_depth) (and_congr (normalization_2206 r0_node) (and_congr (normalization_2212 r0_depth r0_node) (normalization_2209 h r0_depth r0_sign)))))))))

theorem normalization_2228 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_510 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2215 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (or_congr (normalization_2226 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2227 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)))

theorem normalization_2229 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_510 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2219 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2228 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_483 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_507 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_510 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_361 (shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))
  have hn := ht
  exact Iff.mpr (normalization_2229 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

-- Checked replay of mp.
theorem replay_484 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) : (formula_510 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact Iff.mp (replay_483 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_482 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i30)

abbrev shared_expr_Repair014_21 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((¬ (r0_node ≥ (0 : Int))) ∨ (¬ (r0_group ≤ (0 : Int))) ∨ (¬ (r0_group ≥ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_depth ≤ (0 : Int))) ∨ (¬ (r0_depth ≥ (0 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))) ∨ (¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))) ∨ (¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_node ≤ (0 : Int))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_level ≤ (0 : Int))) ∨ (¬ (r0_level ≥ (0 : Int))))
abbrev formula_511 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_21 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair014_22 (h r0_depth r0_sign : Int) : Prop := (((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int)))) ∧ ((¬ ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int)))))))
abbrev shared_expr_Repair014_23 (h r0_depth r0_sign : Int) : Prop := ((shared_expr_Repair014_22 h r0_depth r0_sign) ∨ ((¬ ((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int))))) ∧ (¬ ((¬ (r0_sign ≤ (2 : Int))) ∨ (¬ (r0_sign ≥ (2 : Int)))))))
abbrev formula_512 (h r0_depth r0_sign : Int) : Prop := (shared_expr_Repair014_23 h r0_depth r0_sign)

abbrev shared_expr_Repair014_24 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((¬ (r0_node ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int))) ∨ (¬ (r0_group ≤ (0 : Int))) ∨ (¬ (r0_group ≥ (0 : Int))) ∨ (¬ (r0_mode ≥ (0 : Int))) ∨ (¬ (r0_kind ≤ (1 : Int))) ∨ (¬ (r0_kind ≥ (1 : Int))) ∨ (¬ (r0_depth ≥ (0 : Int))) ∨ (¬ (formula_512 h r0_depth r0_sign)) ∨ (¬ ((¬ ((¬ (r0_node ≤ (0 : Int))) ∨ (¬ (r0_node ≥ (0 : Int))))) ∨ (¬ (r0_depth ≤ (0 : Int))) ∨ (¬ (r0_depth ≥ (0 : Int))))) ∨ (¬ (r0_mode ≤ (0 : Int))) ∨ (¬ (r0_level ≤ (0 : Int))) ∨ (¬ (r0_level ≥ (0 : Int))))
abbrev formula_513 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_24 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

abbrev shared_expr_Repair014_25 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((¬ (formula_511 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ∨ (¬ (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ∨ (¬ (formula_513 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)))
abbrev formula_514 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := (shared_expr_Repair014_25 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)

theorem normalized_362 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p14 ∧ (¬ p15)) ∧ (¬ p3) ∧ (¬ (¬ p16)) ∧ (¬ p4) ∧ (¬ p17) ∧ ((p18 ∧ (¬ p6)) ∨ (p19 ∧ (¬ p18))) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p1 ∧ (¬ p14)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (¬ p9) ∧ (¬ p20) ∧ (¬ p11) ∧ ((¬ (p8 ∧ (¬ p9))) ∨ (p10 ∧ (¬ p11))) ∧ ((((¬ p20) ∧ p21) ∧ (p22 ∧ (¬ p23))) ∨ ((¬ ((¬ p20) ∧ p21)) ∧ ((p12 ∧ (¬ p13)) ∨ (p23 ∧ (¬ p12))))))) ↔ ((¬ ((¬ (¬ p11)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ (¬ p3)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ (¬ p1)) ∨ (¬ p12) ∨ (¬ (¬ p13)) ∨ (¬ p0) ∨ (¬ p10) ∨ (¬ p2) ∨ (¬ p4) ∨ (¬ (¬ p5)))) ∨ (¬ ((¬ p16) ∨ (¬ (¬ p11)) ∨ (¬ ((¬ ((¬ p18) ∨ (¬ (¬ p6)))) ∨ (¬ ((¬ p19) ∨ (¬ (¬ p18)))))) ∨ (¬ (¬ p3)) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ p12) ∨ (¬ (¬ p13)) ∨ (¬ p10) ∨ (¬ (¬ p17)) ∨ (¬ p14) ∨ (¬ (¬ p15)) ∨ (¬ (¬ p4)))) ∨ (¬ ((¬ (¬ p11)) ∨ (¬ (¬ p20)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ (¬ p3)) ∨ (¬ p1) ∨ (¬ (¬ p14)) ∨ (¬ (¬ p9)) ∨ (¬ ((((¬ p21) ∨ (¬ (¬ p20))) ∧ ((¬ ((¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p23) ∨ (¬ (¬ p12)))))) ∨ ((¬ ((¬ p21) ∨ (¬ (¬ p20)))) ∧ (¬ ((¬ p22) ∨ (¬ (¬ p23))))))) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ (¬ p11)))) ∨ (¬ p8) ∨ (¬ (¬ p9)))) ∨ (¬ p2) ∨ (¬ p4) ∨ (¬ (¬ p5)))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2230 (r0_node : Int) : (¬ (r0_node ≥ (0 : Int))) ↔ (¬ (¬ ((r0_node) ≤ (-1 : Int)))) := (not_congr (normalization_2206 r0_node))

theorem normalization_2231 (r0_group : Int) : (r0_group ≤ (0 : Int)) ↔ ((r0_group) ≤ (0 : Int)) := by
  omega

theorem normalization_2232 (r0_group : Int) : (¬ (r0_group ≤ (0 : Int))) ↔ (¬ ((r0_group) ≤ (0 : Int))) := (not_congr (normalization_2231 r0_group))

theorem normalization_2233 (r0_group : Int) : (r0_group ≥ (0 : Int)) ↔ (¬ ((r0_group) ≤ (-1 : Int))) := by
  omega

theorem normalization_2234 (r0_group : Int) : (¬ (r0_group ≥ (0 : Int))) ↔ (¬ (¬ ((r0_group) ≤ (-1 : Int)))) := (not_congr (normalization_2233 r0_group))

theorem normalization_2235 (r0_depth : Int) : (r0_depth ≤ (0 : Int)) ↔ ((r0_depth) ≤ (0 : Int)) := by
  omega

theorem normalization_2236 (r0_depth : Int) : (¬ (r0_depth ≤ (0 : Int))) ↔ (¬ ((r0_depth) ≤ (0 : Int))) := (not_congr (normalization_2235 r0_depth))

theorem normalization_2237 (r0_depth : Int) : (¬ (r0_depth ≥ (0 : Int))) ↔ (¬ (¬ ((r0_depth) ≤ (-1 : Int)))) := (not_congr (normalization_2204 r0_depth))

theorem normalization_2238 (r0_node : Int) : (r0_node ≤ (0 : Int)) ↔ ((r0_node) ≤ (0 : Int)) := by
  omega

theorem normalization_2239 (r0_node : Int) : (¬ (r0_node ≤ (0 : Int))) ↔ (¬ ((r0_node) ≤ (0 : Int))) := (not_congr (normalization_2238 r0_node))

theorem normalization_2240 (r0_level : Int) : (r0_level ≤ (0 : Int)) ↔ ((r0_level) ≤ (0 : Int)) := by
  omega

theorem normalization_2241 (r0_level : Int) : (¬ (r0_level ≤ (0 : Int))) ↔ (¬ ((r0_level) ≤ (0 : Int))) := (not_congr (normalization_2240 r0_level))

theorem normalization_2242 (r0_level : Int) : (r0_level ≥ (0 : Int)) ↔ (¬ ((r0_level) ≤ (-1 : Int))) := by
  omega

theorem normalization_2243 (r0_level : Int) : (¬ (r0_level ≥ (0 : Int))) ↔ (¬ (¬ ((r0_level) ≤ (-1 : Int)))) := (not_congr (normalization_2242 r0_level))

abbrev shared_expr_Repair014_26 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((¬ (¬ ((r0_node) ≤ (-1 : Int)))) ∨ (¬ ((r0_group) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r0_kind) ≤ (1 : Int)))) ∨ (¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (¬ ((r0_kind) ≤ (2 : Int))) ∨ (¬ ((r0_node) ≤ (0 : Int))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((r0_level) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_level) ≤ (-1 : Int)))))
theorem normalization_2244 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_511 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_26 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2230 r0_node) (or_congr (normalization_2232 r0_group) (or_congr (normalization_2234 r0_group) (or_congr (normalization_1752 r0_mode) (or_congr (normalization_2236 r0_depth) (or_congr (normalization_2237 r0_depth) (or_congr (normalization_2029 r0_kind) (or_congr (normalization_2043 r0_sign) (or_congr (normalization_2045 r0_sign) (or_congr (normalization_2027 r0_kind) (or_congr (normalization_2239 r0_node) (or_congr (normalization_1751 r0_mode) (or_congr (normalization_2241 r0_level) (normalization_2243 r0_level))))))))))))))

theorem normalization_2245 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (¬ (formula_511 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ (¬ (shared_expr_Repair014_26 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (not_congr (normalization_2244 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

theorem normalization_2246 (r0_group : Int) : (r0_group ≤ (2 : Int)) ↔ ((r0_group) ≤ (2 : Int)) := by
  omega

theorem normalization_2247 (r0_group : Int) : (¬ (r0_group ≤ (2 : Int))) ↔ (¬ ((r0_group) ≤ (2 : Int))) := (not_congr (normalization_2246 r0_group))

theorem normalization_2248 (r0_group : Int) : (r0_group ≥ (2 : Int)) ↔ (¬ ((r0_group) ≤ (1 : Int))) := by
  omega

theorem normalization_2249 (r0_group : Int) : (¬ (r0_group ≥ (2 : Int))) ↔ (¬ (¬ ((r0_group) ≤ (1 : Int)))) := (not_congr (normalization_2248 r0_group))

theorem normalization_2250 (r0_group : Int) : ((¬ (r0_group ≤ (2 : Int))) ∨ (¬ (r0_group ≥ (2 : Int)))) ↔ ((¬ ((r0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (1 : Int))))) := (or_congr (normalization_2247 r0_group) (normalization_2249 r0_group))

theorem normalization_2251 (r0_group : Int) : (¬ ((¬ (r0_group ≤ (2 : Int))) ∨ (¬ (r0_group ≥ (2 : Int))))) ↔ (¬ ((¬ ((r0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (1 : Int)))))) := (not_congr (normalization_2250 r0_group))

theorem normalization_2252 (r0_group : Int) : ((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r0_group ≤ (2 : Int))) ∨ (¬ (r0_group ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (1 : Int))))))) := (or_congr (normalization_1764 r0_group) (normalization_2251 r0_group))

theorem normalization_2253 (r0_group : Int) : (¬ ((¬ ((¬ (r0_group ≤ (1 : Int))) ∨ (¬ (r0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r0_group ≤ (2 : Int))) ∨ (¬ (r0_group ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (1 : Int)))))))) := (not_congr (normalization_2252 r0_group))

theorem normalization_2254 (h r0_level : Int) : (¬ ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2225 h r0_level))

theorem normalization_2255 (r0_level : Int) : (¬ (r0_level ≥ (1 : Int))) ↔ (¬ (¬ ((r0_level) ≤ (0 : Int)))) := (not_congr (normalization_2191 r0_level))

abbrev shared_expr_Repair014_27 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((¬ ((r0_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r0_node) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r0_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r0_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth) ≤ (-1 : Int)))) ∨ (¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))) ∨ (¬ ((r0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)))) ∨ (¬ ((r0_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r0_level) ≤ (0 : Int)))))
theorem normalization_2256 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_27 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2223 r0_mode) (or_congr (normalization_2230 r0_node) (or_congr (normalization_2253 r0_group) (or_congr (normalization_1752 r0_mode) (or_congr (normalization_2236 r0_depth) (or_congr (normalization_2237 r0_depth) (or_congr (normalization_2043 r0_sign) (or_congr (normalization_2045 r0_sign) (or_congr (normalization_2239 r0_node) (or_congr (normalization_2254 h r0_level) (or_congr (normalization_1670 r0_kind) (or_congr (normalization_1671 r0_kind) (normalization_2255 r0_level)))))))))))))

theorem normalization_2257 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (¬ (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ (¬ (shared_expr_Repair014_27 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (not_congr (normalization_2256 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

theorem normalization_2258 (h r0_depth : Int) : ((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int)))) ↔ ((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_1647 h r0_depth) (normalization_2050 h r0_depth))

theorem normalization_2259 (r0_sign : Int) : ((¬ ((¬ (r0_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int))))))) := (or_congr (normalization_2072 r0_sign) (normalization_2081 r0_sign))

abbrev shared_expr_Repair014_28 (h r0_depth r0_sign : Int) : Prop := (((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((r0_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r0_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (0 : Int))))))))
abbrev shared_expr_Repair014_29 (h r0_depth r0_sign : Int) : Prop := ((shared_expr_Repair014_28 h r0_depth r0_sign) ∨ ((¬ ((¬ ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((r0_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r0_sign) ≤ (1 : Int))))))))
theorem normalization_2260 (h r0_depth r0_sign : Int) : (formula_512 h r0_depth r0_sign) ↔ (shared_expr_Repair014_29 h r0_depth r0_sign) := (or_congr (and_congr (normalization_2258 h r0_depth) (normalization_2259 r0_sign)) (and_congr (not_congr (normalization_2258 h r0_depth)) (normalization_2074 r0_sign)))

theorem normalization_2261 (h r0_depth r0_sign : Int) : (¬ (formula_512 h r0_depth r0_sign)) ↔ (¬ (shared_expr_Repair014_29 h r0_depth r0_sign)) := (not_congr (normalization_2260 h r0_depth r0_sign))

theorem normalization_2262 (r0_node : Int) : ((¬ (r0_node ≤ (0 : Int))) ∨ (¬ (r0_node ≥ (0 : Int)))) ↔ ((¬ ((r0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node) ≤ (-1 : Int))))) := (or_congr (normalization_2239 r0_node) (normalization_2230 r0_node))

theorem normalization_2263 (r0_node : Int) : (¬ ((¬ (r0_node ≤ (0 : Int))) ∨ (¬ (r0_node ≥ (0 : Int))))) ↔ (¬ ((¬ ((r0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node) ≤ (-1 : Int)))))) := (not_congr (normalization_2262 r0_node))

theorem normalization_2264 (r0_depth r0_node : Int) : ((¬ ((¬ (r0_node ≤ (0 : Int))) ∨ (¬ (r0_node ≥ (0 : Int))))) ∨ (¬ (r0_depth ≤ (0 : Int))) ∨ (¬ (r0_depth ≥ (0 : Int)))) ↔ ((¬ ((¬ ((r0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node) ≤ (-1 : Int)))))) ∨ (¬ ((r0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth) ≤ (-1 : Int))))) := (or_congr (normalization_2263 r0_node) (or_congr (normalization_2236 r0_depth) (normalization_2237 r0_depth)))

theorem normalization_2265 (r0_depth r0_node : Int) : (¬ ((¬ ((¬ (r0_node ≤ (0 : Int))) ∨ (¬ (r0_node ≥ (0 : Int))))) ∨ (¬ (r0_depth ≤ (0 : Int))) ∨ (¬ (r0_depth ≥ (0 : Int))))) ↔ (¬ ((¬ ((¬ ((r0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node) ≤ (-1 : Int)))))) ∨ (¬ ((r0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth) ≤ (-1 : Int)))))) := (not_congr (normalization_2264 r0_depth r0_node))

abbrev shared_expr_Repair014_30 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((¬ (¬ ((r0_node) ≤ (-1 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)))) ∨ (¬ ((r0_group) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_group) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r0_mode) ≤ (-1 : Int)))) ∨ (¬ ((r0_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r0_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((r0_depth) ≤ (-1 : Int)))) ∨ (¬ (shared_expr_Repair014_29 h r0_depth r0_sign)) ∨ (¬ ((¬ ((¬ ((r0_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_node) ≤ (-1 : Int)))))) ∨ (¬ ((r0_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_depth) ≤ (-1 : Int)))))) ∨ (¬ ((r0_mode) ≤ (0 : Int))) ∨ (¬ ((r0_level) ≤ (0 : Int))) ∨ (¬ (¬ ((r0_level) ≤ (-1 : Int)))))
theorem normalization_2266 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_513 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_30 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2230 r0_node) (or_congr (normalization_2050 h r0_depth) (or_congr (normalization_2232 r0_group) (or_congr (normalization_2234 r0_group) (or_congr (normalization_1752 r0_mode) (or_congr (normalization_2103 r0_kind) (or_congr (normalization_2105 r0_kind) (or_congr (normalization_2237 r0_depth) (or_congr (normalization_2261 h r0_depth r0_sign) (or_congr (normalization_2265 r0_depth r0_node) (or_congr (normalization_1751 r0_mode) (or_congr (normalization_2241 r0_level) (normalization_2243 r0_level)))))))))))))

theorem normalization_2267 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (¬ (formula_513 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ (¬ (shared_expr_Repair014_30 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (not_congr (normalization_2266 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

abbrev shared_expr_Repair014_31 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : Prop := ((¬ (shared_expr_Repair014_26 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ∨ (¬ (shared_expr_Repair014_27 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ∨ (¬ (shared_expr_Repair014_30 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)))
theorem normalization_2268 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : (formula_514 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_31 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := (or_congr (normalization_2245 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (or_congr (normalization_2257 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2267 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)))

theorem normalization_2269 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_510 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_514 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) ↔ ((shared_expr_Repair014_17 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (shared_expr_Repair014_31 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := (iff_congr (normalization_2228 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (normalization_2268 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))

-- Checked replay of rewrite.
theorem replay_485 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_510 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ (formula_514 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) := by
  classical
  have ht := (normalized_362 ((r0_kind) ≤ (2 : Int)) ((r0_kind) ≤ (1 : Int)) ((r0_mode) ≤ (0 : Int)) ((r0_mode) ≤ (-1 : Int)) ((r0_level) ≤ (0 : Int)) ((r0_level) ≤ (-1 : Int)) ((r0_group) ≤ (0 : Int)) ((r0_group) ≤ (-1 : Int)) ((r0_depth) ≤ (0 : Int)) ((r0_depth) ≤ (-1 : Int)) ((r0_node) ≤ (0 : Int)) ((r0_node) ≤ (-1 : Int)) ((r0_sign) ≤ (0 : Int)) ((r0_sign) ≤ (-1 : Int)) ((r0_kind) ≤ (0 : Int)) ((r0_kind) ≤ (-1 : Int)) ((r0_mode) ≤ (5 : Int)) ((h + ((-1 : Int) * r0_level)) ≤ (-1 : Int)) ((r0_group) ≤ (1 : Int)) ((r0_group) ≤ (2 : Int)) ((h + ((-1 : Int) * r0_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int)) ((r0_sign) ≤ (2 : Int)) ((r0_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2269 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) hn

-- Checked replay of mp.
theorem replay_486 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) : (formula_514 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact Iff.mp (replay_485 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (replay_484 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i30)

theorem propositional_363 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ ((((¬ p8) ∨ (¬ p1)) ∧ ((¬ ((¬ p9) ∨ (¬ p10))) ∨ (¬ ((¬ p11) ∨ (¬ p12))))) ∨ ((¬ ((¬ p8) ∨ (¬ p1))) ∧ (¬ ((¬ p13) ∨ (¬ p14)))))) ∨ (¬ ((¬ ((¬ p15) ∨ (¬ p0))) ∨ (¬ p16) ∨ (¬ p7))) ∨ (¬ p17) ∨ (¬ p18) ∨ (¬ p19)) ∨ p17) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_487 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_513 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (r0_mode ≤ (0 : Int))) := by
  exact (propositional_363 (r0_node ≥ (0 : Int)) ((h + ((-1 : Int) * r0_depth)) ≥ (0 : Int)) (r0_group ≤ (0 : Int)) (r0_group ≥ (0 : Int)) (r0_mode ≥ (0 : Int)) (r0_kind ≤ (1 : Int)) (r0_kind ≥ (1 : Int)) (r0_depth ≥ (0 : Int)) ((h + ((-1 : Int) * r0_depth)) ≤ (0 : Int)) (r0_sign ≤ (0 : Int)) (r0_sign ≥ (0 : Int)) (r0_sign ≤ (1 : Int)) (r0_sign ≥ (1 : Int)) (r0_sign ≤ (2 : Int)) (r0_sign ≥ (2 : Int)) (r0_node ≤ (0 : Int)) (r0_depth ≤ (0 : Int)) (r0_mode ≤ (0 : Int)) (r0_level ≤ (0 : Int)) (r0_level ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_488 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i31 : (¬ (r0_mode ≤ (0 : Int)))) : (formula_513 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact (Or.elim (replay_487 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i31 t0))))

theorem propositional_364 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p11) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_489 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_511 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (r0_mode ≤ (0 : Int))) := by
  exact (propositional_364 (r0_node ≥ (0 : Int)) (r0_group ≤ (0 : Int)) (r0_group ≥ (0 : Int)) (r0_mode ≥ (0 : Int)) (r0_depth ≤ (0 : Int)) (r0_depth ≥ (0 : Int)) (r0_kind ≥ (2 : Int)) (r0_sign ≤ (0 : Int)) (r0_sign ≥ (0 : Int)) (r0_kind ≤ (2 : Int)) (r0_node ≤ (0 : Int)) (r0_mode ≤ (0 : Int)) (r0_level ≤ (0 : Int)) (r0_level ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_490 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i31 : (¬ (r0_mode ≤ (0 : Int)))) : (formula_511 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) := by
  exact (Or.elim (replay_489 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i31 t0))))

-- Checked replay of unit-resolution.
theorem replay_491 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) (i32 : (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) (i31 : (¬ (r0_mode ≤ (0 : Int)))) : False := by
  exact (Or.elim (replay_486 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i30) (fun l0 => (False.elim (l0 (replay_490 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i31)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i32))) (fun t1 => (False.elim (t1 (replay_488 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i31)))))))

-- Checked replay of lemma.
theorem replay_492 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) : ((r0_mode ≤ (0 : Int)) ∨ (¬ (formula_500 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_491 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i30 (Classical.byContradiction (fun q => nc (Or.inr q))) (fun q => nc (Or.inl q)))

-- Checked replay of th-lemma.
theorem replay_493 (r0_mode : Int) : ((¬ (r0_mode ≤ (0 : Int))) ∨ (r0_mode ≤ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_494 (r0_mode : Int) : ((¬ (r0_mode ≤ (1 : Int))) ∨ (¬ (r0_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_495 (r0_mode : Int) : ((r0_mode ≥ (2 : Int)) ∨ (¬ (r0_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_496 (r0_mode : Int) : ((r0_mode ≥ (3 : Int)) ∨ (¬ (r0_mode ≥ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_497 (c2_depth r0_level : Int) : ((r0_level ≤ (0 : Int)) ∨ (¬ (c2_depth ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_498 (c1_level r0_level : Int) : ((c1_level ≤ (0 : Int)) ∨ (¬ (r0_level ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_365 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_499 (c1_group c1_level c1_mode r0_group r0_level r0_mode : Int) : ((formula_345 c1_group c1_level c1_mode r0_group r0_level r0_mode) ∨ ((r0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) := by
  exact (propositional_365 ((r0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) ((r0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ((r0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ((r0_group + ((-1 : Int) * c1_group)) ≤ (0 : Int)) ((r0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair014_32 (r0_node r1_node : Int) : Prop := (((¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Repair014_33 (r0_node r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))))
abbrev formula_515 (r0_node r1_node r1_sign : Int) : Prop := ((shared_expr_Repair014_32 r0_node r1_node) ∨ (shared_expr_Repair014_33 r0_node r1_node r1_sign))

abbrev shared_expr_Repair014_34 (r0_node r1_node : Int) : Prop := (((¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Repair014_35 (r0_node r0_sign r1_node : Int) : Prop := ((¬ ((¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int))))))
abbrev formula_516 (r0_node r0_sign r1_node : Int) : Prop := ((shared_expr_Repair014_34 r0_node r1_node) ∨ (shared_expr_Repair014_35 r0_node r0_sign r1_node))

abbrev shared_expr_Repair014_36 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (1 : Int))) ∨ (formula_515 r0_node r1_node r1_sign)))
abbrev shared_expr_Repair014_37 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := ((shared_expr_Repair014_36 r0_depth r0_node r1_depth r1_node r1_sign) ∨ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (-1 : Int))))) ∧ (formula_516 r0_node r0_sign r1_node)))
abbrev formula_517 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_37 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair014_38 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((¬ ((¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (r0_sign ≥ (1 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r0_sign ≤ (1 : Int))))))
abbrev shared_expr_Repair014_39 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((((¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int)))) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int)))) ∨ (shared_expr_Repair014_38 r0_node r0_sign r1_node r1_sign))
abbrev formula_518 (r0_node r0_sign r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_39 r0_node r0_sign r1_node r1_sign)

abbrev shared_expr_Repair014_40 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))) ∧ (formula_517 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ∨ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (0 : Int))))) ∧ (formula_518 r0_node r0_sign r1_node r1_sign)))
abbrev formula_519 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_40 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair014_41 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (formula_519 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))))
abbrev formula_520 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_41 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair014_42 (r0_group r0_mode r1_group r1_mode : Int) : Prop := ((((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)))) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int))))) ∧ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)))))
abbrev formula_521 (r0_group r0_mode r1_group r1_mode : Int) : Prop := (shared_expr_Repair014_42 r0_group r0_mode r1_group r1_mode)

abbrev shared_expr_Repair014_43 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := ((((¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)))) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int))))) ∧ (formula_521 r0_group r0_mode r1_group r1_mode)))
abbrev formula_522 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair014_43 r0_group r0_level r0_mode r1_group r1_level r1_mode)

abbrev shared_expr_Repair014_44 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))) ∨ ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))))
abbrev formula_523 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (shared_expr_Repair014_44 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)

abbrev shared_expr_Repair014_45 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) ∧ (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) ∨ ((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∧ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)))
abbrev formula_524 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_45 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair014_46 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∨ (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)) ∨ (¬ (formula_524 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))
abbrev formula_525 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_46 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem propositional_366 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ p0) ∨ (¬ p1) ∨ (¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ ((¬ p2) ∨ (¬ p3) ∨ (((p4 ↔ p5) ∧ ((((¬ p6) ∨ (¬ p7)) ∧ (¬ p7)) ∨ ((¬ ((¬ p6) ∨ (¬ p7))) ∧ ((((¬ p8) ∨ (¬ p9)) ∧ (¬ p9)) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ (¬ p10)))))) ∨ ((¬ (p4 ↔ p5)) ∧ p4))))))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_500 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_525 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (propositional_366 ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) (r0_mode ≥ (4 : Int)) (r1_mode ≥ (4 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)) ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair014_47 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := ((¬ (¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))))) ∧ (((r0_level ≠ r1_level) ∧ (r0_level < r1_level)) ∨ ((¬ (r0_level ≠ r1_level)) ∧ (((r0_mode ≠ r1_mode) ∧ (r0_mode < r1_mode)) ∨ ((¬ (r0_mode ≠ r1_mode)) ∧ (r0_group < r1_group))))))
abbrev formula_526 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int))) ∨ (shared_expr_Repair014_47 r0_group r0_level r0_mode r1_group r1_level r1_mode))

abbrev shared_expr_Repair014_48 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := ((((r1_depth + (1 : Int)) = r0_depth) ∧ (((r1_node = (r0_node / (2 : Int))) ∧ (r1_sign = (0 : Int))) ∨ ((¬ (r1_node = (r0_node / (2 : Int)))) ∧ ((r0_node / (2 : Int)) < r1_node)))) ∨ ((¬ ((r1_depth + (1 : Int)) = r0_depth)) ∧ True))
abbrev formula_527 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_48 r0_depth r0_node r1_depth r1_node r1_sign)

abbrev shared_expr_Repair014_49 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := ((((r0_depth + (1 : Int)) = r1_depth) ∧ (((r0_node = (r1_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r1_node / (2 : Int)))) ∧ (r0_node < (r1_node / (2 : Int)))))) ∨ ((¬ ((r0_depth + (1 : Int)) = r1_depth)) ∧ (formula_527 r0_depth r0_node r1_depth r1_node r1_sign)))
abbrev formula_528 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_49 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair014_50 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((r0_depth = r1_depth) ∧ (((r0_node = r1_node) ∧ ((r0_sign = (1 : Int)) ∧ (r1_sign = (0 : Int)))) ∨ ((¬ (r0_node = r1_node)) ∧ (r0_node < r1_node)))) ∨ ((¬ (r0_depth = r1_depth)) ∧ (formula_528 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
abbrev formula_529 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_50 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair014_51 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((r0_kind = (2 : Int)) ∧ (False ∧ (r1_kind = (1 : Int)))) ∨ ((¬ (r0_kind = (2 : Int))) ∧ (((r1_kind = (2 : Int)) ∧ True) ∨ ((¬ (r1_kind = (2 : Int))) ∧ (formula_529 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))))
abbrev formula_530 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_51 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)

abbrev shared_expr_Repair014_52 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r0_kind = (0 : Int)) ∧ (((r1_kind = (0 : Int)) ∧ (formula_526 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ (r1_kind = (0 : Int))) ∧ True))) ∨ ((¬ (r0_kind = (0 : Int))) ∧ (((r1_kind = (0 : Int)) ∧ False) ∨ ((¬ (r1_kind = (0 : Int))) ∧ (formula_530 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))))
abbrev formula_531 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_52 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair014_53 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (((r0_level = r1_level) ∧ (((r0_mode = r1_mode) ∧ (¬ (r1_group ≤ r0_group))) ∨ ((¬ (r0_mode = r1_mode)) ∧ (¬ (r1_mode ≤ r0_mode))))) ∨ ((¬ (r0_level = r1_level)) ∧ (¬ (r1_level ≤ r0_level)))))
abbrev formula_532 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := ((shared_expr_Repair014_53 r0_group r0_level r0_mode r1_group r1_level r1_mode) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int))))

abbrev shared_expr_Repair014_54 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := ((¬ (r0_depth = ((-1 : Int) + r1_depth))) ∧ ((¬ (r1_depth = ((-1 : Int) + r0_depth))) ∨ (((r1_node = (r0_node / (2 : Int))) ∧ (r1_sign = (0 : Int))) ∨ ((¬ (r1_node = (r0_node / (2 : Int)))) ∧ (¬ (r1_node ≤ (r0_node / (2 : Int))))))))
abbrev shared_expr_Repair014_55 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((r0_depth = ((-1 : Int) + r1_depth)) ∧ (((r0_node = (r1_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r1_node / (2 : Int)))) ∧ (¬ ((r1_node / (2 : Int)) ≤ r0_node))))) ∨ (shared_expr_Repair014_54 r0_depth r0_node r1_depth r1_node r1_sign))
abbrev formula_533 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_55 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair014_56 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((r0_depth = r1_depth) ∧ (((r0_node = r1_node) ∧ ((r0_sign = (1 : Int)) ∧ (r1_sign = (0 : Int)))) ∨ ((¬ (r0_node = r1_node)) ∧ (¬ (r1_node ≤ r0_node))))) ∨ ((¬ (r0_depth = r1_depth)) ∧ (formula_533 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
abbrev formula_534 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_56 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)

abbrev shared_expr_Repair014_57 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r0_kind = (0 : Int)) ∧ ((¬ (r1_kind = (0 : Int))) ∨ (formula_532 r0_group r0_level r0_mode r1_group r1_level r1_mode))) ∨ ((¬ (r0_kind = (0 : Int))) ∧ ((¬ (r1_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r1_kind = (2 : Int)) ∨ (formula_534 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))))
abbrev formula_535 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_57 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair014_58 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_535 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_536 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair014_58 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_367 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (False ∧ (p10 ∧ (¬ p11)))) ∨ ((¬ p9) ∧ ((p12 ∧ True) ∨ ((¬ p12) ∧ ((p13 ∧ ((p14 ∧ p15) ∨ ((¬ p14) ∧ p16))) ∨ ((¬ p13) ∧ ((p17 ∧ p18) ∨ ((¬ p17) ∧ ((p19 ∧ ((p20 ∧ p21) ∨ ((¬ p20) ∧ p22))) ∨ ((¬ p19) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ (¬ p9) ∧ (p12 ∨ ((p13 ∧ ((p14 ∧ p15) ∨ ((¬ p14) ∧ (¬ (¬ p16))))) ∨ ((¬ p13) ∧ ((p17 ∧ p18) ∨ ((¬ p17) ∧ ((¬ p19) ∨ ((p20 ∧ p21) ∨ ((¬ p20) ∧ (¬ (¬ p22)))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2270 (r1_kind : Int) : (r1_kind = (0 : Int)) ↔ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2271 (r1_mode : Int) : (r1_mode ≥ (4 : Int)) ↔ (¬ ((r1_mode) ≤ (3 : Int))) := by
  omega

theorem normalization_2272 (r0_mode r1_mode : Int) : (¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_1963 r0_mode) (normalization_2271 r1_mode)))

theorem normalization_2273 (r0_level r1_level : Int) : (r0_level ≠ r1_level) ↔ (¬ (((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_2274 (r0_level r1_level : Int) : (r0_level < r1_level) ↔ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2275 (r0_mode r1_mode : Int) : (r0_mode ≠ r1_mode) ↔ (¬ (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_2276 (r0_mode r1_mode : Int) : (r0_mode < r1_mode) ↔ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_2277 (r0_group r1_group : Int) : (r0_group < r1_group) ↔ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair014_59 (r0_group r0_mode r1_group r1_mode : Int) : Prop := (((¬ (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) ∧ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))))) ∧ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))))
theorem normalization_2278 (r0_group r0_mode r1_group r1_mode : Int) : (((r0_mode ≠ r1_mode) ∧ (r0_mode < r1_mode)) ∨ ((¬ (r0_mode ≠ r1_mode)) ∧ (r0_group < r1_group))) ↔ (shared_expr_Repair014_59 r0_group r0_mode r1_group r1_mode) := (or_congr (and_congr (normalization_2275 r0_mode r1_mode) (normalization_2276 r0_mode r1_mode)) (and_congr (not_congr (normalization_2275 r0_mode r1_mode)) (normalization_2277 r0_group r1_group)))

abbrev shared_expr_Repair014_60 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ (((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair014_59 r0_group r0_mode r1_group r1_mode)))
theorem normalization_2279 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (((r0_level ≠ r1_level) ∧ (r0_level < r1_level)) ∨ ((¬ (r0_level ≠ r1_level)) ∧ (((r0_mode ≠ r1_mode) ∧ (r0_mode < r1_mode)) ∨ ((¬ (r0_mode ≠ r1_mode)) ∧ (r0_group < r1_group))))) ↔ (shared_expr_Repair014_60 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2273 r0_level r1_level) (normalization_2274 r0_level r1_level)) (and_congr (not_congr (normalization_2273 r0_level r1_level)) (normalization_2278 r0_group r0_mode r1_group r1_mode)))

abbrev shared_expr_Repair014_61 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int))))) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair014_60 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
theorem normalization_2280 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (formula_526 r0_group r0_level r0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair014_61 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2272 r0_mode r1_mode) (normalization_1963 r0_mode)) (and_congr (not_congr (normalization_2272 r0_mode r1_mode)) (normalization_2279 r0_group r0_level r0_mode r1_group r1_level r1_mode)))

abbrev shared_expr_Repair014_62 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair014_61 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_2281 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : (((r1_kind = (0 : Int)) ∧ (formula_526 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ (r1_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Repair014_62 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := (or_congr (and_congr (normalization_2270 r1_kind) (normalization_2280 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_2270 r1_kind)) (normalization_305)))

theorem normalization_2282 (r1_kind : Int) : (r1_kind = (1 : Int)) ↔ (((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) := by
  omega

theorem normalization_2283 (r1_kind : Int) : (False ∧ (r1_kind = (1 : Int))) ↔ (False ∧ (((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int))))) := (and_congr (normalization_1253) (normalization_2282 r1_kind))

theorem normalization_2284 (r1_kind : Int) : (r1_kind = (2 : Int)) ↔ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) := by
  omega

theorem normalization_2285 (r0_depth r1_depth : Int) : (r0_depth = r1_depth) ↔ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2286 (r0_node r1_node : Int) : (r0_node = r1_node) ↔ (((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2287 (r1_sign : Int) : (r1_sign = (0 : Int)) ↔ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2288 (r0_sign r1_sign : Int) : ((r0_sign = (1 : Int)) ∧ (r1_sign = (0 : Int))) ↔ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))) := (and_congr (normalization_1497 r0_sign) (normalization_2287 r1_sign))

theorem normalization_2289 (r0_node r1_node : Int) : (r0_node < r1_node) ↔ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair014_63 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ∧ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))))
abbrev shared_expr_Repair014_64 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((shared_expr_Repair014_63 r0_node r0_sign r1_node r1_sign) ∨ ((¬ (((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) ∧ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))
theorem normalization_2290 (r0_node r0_sign r1_node r1_sign : Int) : (((r0_node = r1_node) ∧ ((r0_sign = (1 : Int)) ∧ (r1_sign = (0 : Int)))) ∨ ((¬ (r0_node = r1_node)) ∧ (r0_node < r1_node))) ↔ (shared_expr_Repair014_64 r0_node r0_sign r1_node r1_sign) := (or_congr (and_congr (normalization_2286 r0_node r1_node) (normalization_2288 r0_sign r1_sign)) (and_congr (not_congr (normalization_2286 r0_node r1_node)) (normalization_2289 r0_node r1_node)))

theorem normalization_2291 (r0_depth r1_depth : Int) : ((r0_depth + (1 : Int)) = r1_depth) ↔ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2292 (r0_node r1_node : Int) : (r0_node = (r1_node / (2 : Int))) ↔ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2293 (r0_node r1_node : Int) : (r0_node < (r1_node / (2 : Int))) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Repair014_65 (r0_node r1_node : Int) : Prop := ((¬ ((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)))) ∧ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair014_66 (r0_node r0_sign r1_node : Int) : Prop := ((((¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) ∧ (((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair014_65 r0_node r1_node))
theorem normalization_2294 (r0_node r0_sign r1_node : Int) : (((r0_node = (r1_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r1_node / (2 : Int)))) ∧ (r0_node < (r1_node / (2 : Int))))) ↔ (shared_expr_Repair014_66 r0_node r0_sign r1_node) := (or_congr (and_congr (normalization_2292 r0_node r1_node) (normalization_1497 r0_sign)) (and_congr (not_congr (normalization_2292 r0_node r1_node)) (normalization_2293 r0_node r1_node)))

theorem normalization_2295 (r0_depth r1_depth : Int) : ((r1_depth + (1 : Int)) = r0_depth) ↔ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_2296 (r0_node r1_node : Int) : (r1_node = (r0_node / (2 : Int))) ↔ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_2297 (r0_node r1_node : Int) : ((r0_node / (2 : Int)) < r1_node) ↔ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair014_67 (r0_node r1_node : Int) : Prop := ((¬ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair014_68 (r0_node r1_node r1_sign : Int) : Prop := ((((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair014_67 r0_node r1_node))
theorem normalization_2298 (r0_node r1_node r1_sign : Int) : (((r1_node = (r0_node / (2 : Int))) ∧ (r1_sign = (0 : Int))) ∨ ((¬ (r1_node = (r0_node / (2 : Int)))) ∧ ((r0_node / (2 : Int)) < r1_node))) ↔ (shared_expr_Repair014_68 r0_node r1_node r1_sign) := (or_congr (and_congr (normalization_2296 r0_node r1_node) (normalization_2287 r1_sign)) (and_congr (not_congr (normalization_2296 r0_node r1_node)) (normalization_2297 r0_node r1_node)))

abbrev shared_expr_Repair014_69 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := ((((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ∧ (shared_expr_Repair014_68 r0_node r1_node r1_sign)) ∨ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_2299 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : (formula_527 r0_depth r0_node r1_depth r1_node r1_sign) ↔ (shared_expr_Repair014_69 r0_depth r0_node r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2295 r0_depth r1_depth) (normalization_2298 r0_node r1_node r1_sign)) (and_congr (not_congr (normalization_2295 r0_depth r1_depth)) (normalization_305)))

abbrev shared_expr_Repair014_70 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair014_66 r0_node r0_sign r1_node)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair014_69 r0_depth r0_node r1_depth r1_node r1_sign)))
theorem normalization_2300 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_528 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair014_70 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2291 r0_depth r1_depth) (normalization_2294 r0_node r0_sign r1_node)) (and_congr (not_congr (normalization_2291 r0_depth r1_depth)) (normalization_2299 r0_depth r0_node r1_depth r1_node r1_sign)))

abbrev shared_expr_Repair014_71 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair014_64 r0_node r0_sign r1_node r1_sign)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair014_70 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2301 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_529 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair014_71 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2285 r0_depth r1_depth) (normalization_2290 r0_node r0_sign r1_node r1_sign)) (and_congr (not_congr (normalization_2285 r0_depth r1_depth)) (normalization_2300 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))

abbrev shared_expr_Repair014_72 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∧ True) ∨ ((¬ (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair014_71 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2302 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (((r1_kind = (2 : Int)) ∧ True) ∨ ((¬ (r1_kind = (2 : Int))) ∧ (formula_529 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))) ↔ (shared_expr_Repair014_72 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_2284 r1_kind) (normalization_305)) (and_congr (not_congr (normalization_2284 r1_kind)) (normalization_2301 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))

abbrev shared_expr_Repair014_73 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ∧ (False ∧ (((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))))) ∨ ((¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair014_72 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))
theorem normalization_2303 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (formula_530 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) ↔ (shared_expr_Repair014_73 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_1506 r0_kind) (normalization_2283 r1_kind)) (and_congr (not_congr (normalization_1506 r0_kind)) (normalization_2302 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair014_74 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair014_73 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))
theorem normalization_2304 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : (((r1_kind = (0 : Int)) ∧ False) ∨ ((¬ (r1_kind = (0 : Int))) ∧ (formula_530 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign))) ↔ (shared_expr_Repair014_74 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (or_congr (and_congr (normalization_2270 r1_kind) (normalization_1253)) (and_congr (not_congr (normalization_2270 r1_kind)) (normalization_2303 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair014_75 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair014_62 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) ∨ ((¬ (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair014_74 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))
theorem normalization_2305 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair014_75 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_1438 r0_kind) (normalization_2281 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) (and_congr (not_congr (normalization_1438 r0_kind)) (normalization_2304 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

theorem normalization_2306 (r1_kind : Int) : (¬ (r1_kind = (0 : Int))) ↔ (¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) := (not_congr (normalization_2270 r1_kind))

theorem normalization_2307 (r0_mode r1_mode : Int) : ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ↔ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int)))) := (iff_congr (normalization_1963 r0_mode) (normalization_2271 r1_mode))

theorem normalization_2308 (r0_level r1_level : Int) : (r0_level = r1_level) ↔ (((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2309 (r0_mode r1_mode : Int) : (r0_mode = r1_mode) ↔ (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2310 (r0_group r1_group : Int) : (r1_group ≤ r0_group) ↔ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2311 (r0_group r1_group : Int) : (¬ (r1_group ≤ r0_group)) ↔ (¬ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_2310 r0_group r1_group))

theorem normalization_2312 (r0_mode r1_mode : Int) : (r1_mode ≤ r0_mode) ↔ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2313 (r0_mode r1_mode : Int) : (¬ (r1_mode ≤ r0_mode)) ↔ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_2312 r0_mode r1_mode))

abbrev shared_expr_Repair014_76 (r0_group r0_mode r1_group r1_mode : Int) : Prop := (((((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int))))) ∨ ((¬ (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int))))))
theorem normalization_2314 (r0_group r0_mode r1_group r1_mode : Int) : (((r0_mode = r1_mode) ∧ (¬ (r1_group ≤ r0_group))) ∨ ((¬ (r0_mode = r1_mode)) ∧ (¬ (r1_mode ≤ r0_mode)))) ↔ (shared_expr_Repair014_76 r0_group r0_mode r1_group r1_mode) := (or_congr (and_congr (normalization_2309 r0_mode r1_mode) (normalization_2311 r0_group r1_group)) (and_congr (not_congr (normalization_2309 r0_mode r1_mode)) (normalization_2313 r0_mode r1_mode)))

theorem normalization_2315 (r0_level r1_level : Int) : (r1_level ≤ r0_level) ↔ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2316 (r0_level r1_level : Int) : (¬ (r1_level ≤ r0_level)) ↔ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2315 r0_level r1_level))

abbrev shared_expr_Repair014_77 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (((((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair014_76 r0_group r0_mode r1_group r1_mode)) ∨ ((¬ (((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int))))))
theorem normalization_2317 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (((r0_level = r1_level) ∧ (((r0_mode = r1_mode) ∧ (¬ (r1_group ≤ r0_group))) ∨ ((¬ (r0_mode = r1_mode)) ∧ (¬ (r1_mode ≤ r0_mode))))) ∨ ((¬ (r0_level = r1_level)) ∧ (¬ (r1_level ≤ r0_level)))) ↔ (shared_expr_Repair014_77 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2308 r0_level r1_level) (normalization_2314 r0_group r0_mode r1_group r1_mode)) (and_congr (not_congr (normalization_2308 r0_level r1_level)) (normalization_2316 r0_level r1_level)))

abbrev shared_expr_Repair014_78 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := ((((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair014_77 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r1_mode) ≤ (3 : Int))))) ∧ (¬ ((r0_mode) ≤ (3 : Int)))))
theorem normalization_2318 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : (formula_532 r0_group r0_level r0_mode r1_group r1_level r1_mode) ↔ (shared_expr_Repair014_78 r0_group r0_level r0_mode r1_group r1_level r1_mode) := (or_congr (and_congr (normalization_2307 r0_mode r1_mode) (normalization_2317 r0_group r0_level r0_mode r1_group r1_level r1_mode)) (and_congr (not_congr (normalization_2307 r0_mode r1_mode)) (normalization_1963 r0_mode)))

theorem normalization_2319 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((¬ (r1_kind = (0 : Int))) ∨ (formula_532 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ↔ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair014_78 r0_group r0_level r0_mode r1_group r1_level r1_mode)) := (or_congr (normalization_2306 r1_kind) (normalization_2318 r0_group r0_level r0_mode r1_group r1_level r1_mode))

theorem normalization_2320 (r0_kind : Int) : (¬ (r0_kind = (2 : Int))) ↔ (¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) := (not_congr (normalization_1506 r0_kind))

theorem normalization_2321 (r0_node r1_node : Int) : (r1_node ≤ r0_node) ↔ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2322 (r0_node r1_node : Int) : (¬ (r1_node ≤ r0_node)) ↔ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2321 r0_node r1_node))

abbrev shared_expr_Repair014_79 (r0_node r0_sign r1_node r1_sign : Int) : Prop := ((shared_expr_Repair014_63 r0_node r0_sign r1_node r1_sign) ∨ ((¬ (((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int))))))
theorem normalization_2323 (r0_node r0_sign r1_node r1_sign : Int) : (((r0_node = r1_node) ∧ ((r0_sign = (1 : Int)) ∧ (r1_sign = (0 : Int)))) ∨ ((¬ (r0_node = r1_node)) ∧ (¬ (r1_node ≤ r0_node)))) ↔ (shared_expr_Repair014_79 r0_node r0_sign r1_node r1_sign) := (or_congr (and_congr (normalization_2286 r0_node r1_node) (normalization_2288 r0_sign r1_sign)) (and_congr (not_congr (normalization_2286 r0_node r1_node)) (normalization_2322 r0_node r1_node)))

theorem normalization_2324 (r0_depth r1_depth : Int) : (r0_depth = ((-1 : Int) + r1_depth)) ↔ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_2325 (r0_node r1_node : Int) : ((r1_node / (2 : Int)) ≤ r0_node) ↔ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_2326 (r0_node r1_node : Int) : (¬ ((r1_node / (2 : Int)) ≤ r0_node)) ↔ (¬ (((r1_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := (not_congr (normalization_2325 r0_node r1_node))

theorem normalization_2327 (r0_node r0_sign r1_node : Int) : (((r0_node = (r1_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r1_node / (2 : Int)))) ∧ (¬ ((r1_node / (2 : Int)) ≤ r0_node)))) ↔ (shared_expr_Repair014_66 r0_node r0_sign r1_node) := (or_congr (and_congr (normalization_2292 r0_node r1_node) (normalization_1497 r0_sign)) (and_congr (not_congr (normalization_2292 r0_node r1_node)) (normalization_2326 r0_node r1_node)))

theorem normalization_2328 (r0_depth r1_depth : Int) : (r1_depth = ((-1 : Int) + r0_depth)) ↔ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_2329 (r0_depth r1_depth : Int) : (¬ (r1_depth = ((-1 : Int) + r0_depth))) ↔ (¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)))) := (not_congr (normalization_2328 r0_depth r1_depth))

theorem normalization_2330 (r0_node r1_node : Int) : (r1_node ≤ (r0_node / (2 : Int))) ↔ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2331 (r0_node r1_node : Int) : (¬ (r1_node ≤ (r0_node / (2 : Int)))) ↔ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_2330 r0_node r1_node))

abbrev shared_expr_Repair014_80 (r0_node r1_node : Int) : Prop := ((¬ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair014_81 (r0_node r1_node r1_sign : Int) : Prop := ((((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair014_80 r0_node r1_node))
theorem normalization_2332 (r0_node r1_node r1_sign : Int) : (((r1_node = (r0_node / (2 : Int))) ∧ (r1_sign = (0 : Int))) ∨ ((¬ (r1_node = (r0_node / (2 : Int)))) ∧ (¬ (r1_node ≤ (r0_node / (2 : Int)))))) ↔ (shared_expr_Repair014_81 r0_node r1_node r1_sign) := (or_congr (and_congr (normalization_2296 r0_node r1_node) (normalization_2287 r1_sign)) (and_congr (not_congr (normalization_2296 r0_node r1_node)) (normalization_2331 r0_node r1_node)))

theorem normalization_2333 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : ((¬ (r1_depth = ((-1 : Int) + r0_depth))) ∨ (((r1_node = (r0_node / (2 : Int))) ∧ (r1_sign = (0 : Int))) ∨ ((¬ (r1_node = (r0_node / (2 : Int)))) ∧ (¬ (r1_node ≤ (r0_node / (2 : Int))))))) ↔ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair014_81 r0_node r1_node r1_sign)) := (or_congr (normalization_2329 r0_depth r1_depth) (normalization_2332 r0_node r1_node r1_sign))

abbrev shared_expr_Repair014_82 (r0_depth r0_node r1_depth r1_node r1_sign : Int) : Prop := ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair014_81 r0_node r1_node r1_sign)))
abbrev shared_expr_Repair014_83 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair014_66 r0_node r0_sign r1_node)) ∨ (shared_expr_Repair014_82 r0_depth r0_node r1_depth r1_node r1_sign))
theorem normalization_2334 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_533 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair014_83 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2324 r0_depth r1_depth) (normalization_2327 r0_node r0_sign r1_node)) (and_congr (not_congr (normalization_2324 r0_depth r1_depth)) (normalization_2333 r0_depth r0_node r1_depth r1_node r1_sign)))

abbrev shared_expr_Repair014_84 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair014_79 r0_node r0_sign r1_node r1_sign)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair014_83 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2335 (r0_depth r0_node r0_sign r1_depth r1_node r1_sign : Int) : (formula_534 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) ↔ (shared_expr_Repair014_84 r0_depth r0_node r0_sign r1_depth r1_node r1_sign) := (or_congr (and_congr (normalization_2285 r0_depth r1_depth) (normalization_2323 r0_node r0_sign r1_node r1_sign)) (and_congr (not_congr (normalization_2285 r0_depth r1_depth)) (normalization_2334 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))

theorem normalization_2336 (r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((r1_kind = (2 : Int)) ∨ (formula_534 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) ↔ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair014_84 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)) := (or_congr (normalization_2284 r1_kind) (normalization_2335 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))

abbrev shared_expr_Repair014_85 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∧ (¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ∧ ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair014_84 r0_depth r0_node r0_sign r1_depth r1_node r1_sign)))
theorem normalization_2337 (r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (r1_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r1_kind = (2 : Int)) ∨ (formula_534 r0_depth r0_node r0_sign r1_depth r1_node r1_sign))) ↔ (shared_expr_Repair014_85 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) := (and_congr (normalization_2306 r1_kind) (and_congr (normalization_2320 r0_kind) (normalization_2336 r0_depth r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair014_86 (r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair014_78 r0_group r0_level r0_mode r1_group r1_level r1_mode)))
abbrev shared_expr_Repair014_87 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair014_86 r0_group r0_kind r0_level r0_mode r1_group r1_kind r1_level r1_mode) ∨ ((¬ (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair014_85 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))
theorem normalization_2338 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_535 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair014_87 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (and_congr (normalization_1438 r0_kind) (normalization_2319 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) (and_congr (not_congr (normalization_1438 r0_kind)) (normalization_2337 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)))

abbrev shared_expr_Repair014_88 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair014_75 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair014_87 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2339 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_536 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair014_88 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (iff_congr (normalization_2305 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2338 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_501 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_536 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  classical
  have ht := (normalized_367 (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((r0_mode) ≤ (3 : Int)) ((r1_mode) ≤ (3 : Int)) (((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) ((r0_level + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) (((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)))) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (-1 : Int)) ((r0_group + ((-1 : Int) * r1_group)) ≤ (-1 : Int)) (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ((r1_kind) ≤ (1 : Int)) ((r1_kind) ≤ (0 : Int)) (((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) (((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))) ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int))))) ((r0_node + ((-1 : Int) * r1_node)) ≤ (-1 : Int)) (((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-2 : Int)))) (shared_expr_Repair014_66 r0_node r0_sign r1_node) ((¬ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int))) ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (0 : Int))) (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) (((r0_node / (2 : Int)) + ((-1 : Int) * r1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2339 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

end H4Formal.Generated.Repair
