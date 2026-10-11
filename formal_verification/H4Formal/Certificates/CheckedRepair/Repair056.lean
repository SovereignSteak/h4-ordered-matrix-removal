import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair055

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of unit-resolution.
theorem replay_3208 (c0_group r1_group r2_group : Int) (i187 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i188 : (r2_group ≤ (2 : Int))) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i189 : ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) : (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_3201 c0_group r1_group) (fun l0 => (False.elim (l0 i189))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3207 c0_group r1_group r2_group i187 i188 i50)))) (fun t1 => t1))))

theorem propositional_1329 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3209 (c0_group : Int) : (((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (c0_group ≤ (1 : Int))) := by
  exact (propositional_1329 (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3210 (c0_group : Int) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) : (c0_group ≤ (1 : Int)) := by
  exact (Or.elim (replay_3209 c0_group) (fun l0 => (False.elim (i50 l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_3211 (c0_group r1_group r2_group : Int) (i187 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i190 : (¬ (r1_group ≤ (0 : Int)))) (i188 : (r2_group ≤ (2 : Int))) (i50 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i189 : ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) : False := by
  classical
  have k0 := (replay_3208 c0_group r1_group r2_group i187 i188 i50 i189)
  have k1 := i190
  have k2 := (replay_3210 c0_group i50)
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair056_0 (c0_group r1_group r2_group : Int) : Prop := (((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (r1_group ≤ (0 : Int)) ∨ (¬ ((¬ ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int))) ∨ (¬ ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int))))) ∨ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ∨ (¬ (r2_group ≤ (2 : Int))))
abbrev formula_1525 (c0_group r1_group r2_group : Int) : Prop := (shared_expr_Repair056_0 c0_group r1_group r2_group)

-- Checked replay of lemma.
theorem replay_3212 (c0_group r1_group r2_group : Int) : (formula_1525 c0_group r1_group r2_group) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3211 c0_group r1_group r2_group (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q))))) (fun q => nc (Or.inr (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr q)))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))))

-- Checked replay of th-lemma.
theorem replay_3213 (r1_group : Int) : ((¬ (r1_group ≤ (0 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1330 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3214 (r1_group : Int) : (((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∨ (r1_group ≥ (1 : Int))) := by
  exact (propositional_1330 (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)))

abbrev shared_expr_Repair056_1 (r1_group : Int) : Prop := ((¬ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) ∨ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))
abbrev formula_1526 (r1_group : Int) : Prop := (shared_expr_Repair056_1 r1_group)

theorem propositional_1331 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3215 (r1_group : Int) : (formula_1526 r1_group) := by
  exact (propositional_1331 ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))))

theorem propositional_1332 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3216 (r1_group : Int) : (((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))) ∨ (r1_group ≥ (2 : Int))) := by
  exact (propositional_1332 (r1_group ≤ (2 : Int)) (r1_group ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_3217 (r1_group r2_group : Int) : ((¬ (r2_group ≤ (2 : Int))) ∨ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ∨ (¬ (r1_group ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1333 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3218 (r2_group : Int) : (((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (r2_group ≤ (1 : Int))) := by
  exact (propositional_1333 (r2_group ≤ (1 : Int)) (r2_group ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_3219 (r1_group r2_group : Int) : ((¬ (r2_group ≤ (1 : Int))) ∨ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ∨ (¬ (r1_group ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3220 (r1_group r2_group : Int) (i187 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i191 : (r2_group ≤ (1 : Int))) : (¬ (r1_group ≥ (2 : Int))) := by
  exact (Or.elim (replay_3219 r1_group r2_group) (fun l0 => (False.elim (l0 i191))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i187 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3221 (r1_group r2_group : Int) (i187 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i191 : (r2_group ≤ (1 : Int))) : ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))) := by
  exact (Or.elim (replay_3216 r1_group) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3220 r1_group r2_group i187 i191) t0))))

-- Checked replay of th-lemma.
theorem replay_3222 (r1_group r2_group : Int) : ((¬ (r2_group ≤ (1 : Int))) ∨ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ∨ (¬ (r1_group ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_3223 (r1_group r2_group : Int) (i187 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i191 : (r2_group ≤ (1 : Int))) : (¬ (r1_group ≥ (1 : Int))) := by
  exact (Or.elim (replay_3222 r1_group r2_group) (fun l0 => (False.elim (l0 i191))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i187 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3224 (r1_group r2_group : Int) (i187 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i191 : (r2_group ≤ (1 : Int))) : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) := by
  exact (Or.elim (replay_3214 r1_group) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_3223 r1_group r2_group i187 i191) t0))))

-- Checked replay of unit-resolution.
theorem replay_3225 (r1_group r2_group : Int) (i187 : (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))) (i192 : ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) (i191 : (r2_group ≤ (1 : Int))) : False := by
  exact (Or.elim (replay_3215 r1_group) (fun l0 => (False.elim (l0 i192))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3224 r1_group r2_group i187 i191)))) (fun t1 => (False.elim (t1 (replay_3221 r1_group r2_group i187 i191)))))))

abbrev shared_expr_Repair056_2 (r1_group r2_group : Int) : Prop := (((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) ∨ (¬ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) ∨ (¬ (r2_group ≤ (1 : Int))))
abbrev formula_1527 (r1_group r2_group : Int) : Prop := (shared_expr_Repair056_2 r1_group r2_group)

-- Checked replay of lemma.
theorem replay_3226 (r1_group r2_group : Int) : (formula_1527 r1_group r2_group) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3225 r1_group r2_group (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))))

abbrev shared_expr_Repair056_3 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ∨ (formula_596 r1_group r1_mode r2_group r2_mode))
abbrev formula_1528 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair056_3 r1_group r1_level r1_mode r2_group r2_level r2_mode)

theorem propositional_1334 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ p2))) ∨ p0 ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3227 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_1528 r1_group r1_level r1_mode r2_group r2_level r2_mode) := by
  exact (propositional_1334 ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)) (formula_596 r1_group r1_mode r2_group r2_mode))

abbrev shared_expr_Repair056_4 (r1_group r1_mode r2_group r2_mode : Int) : Prop := ((¬ (formula_596 r1_group r1_mode r2_group r2_mode)) ∨ ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ∨ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int))))
abbrev formula_1529 (r1_group r1_mode r2_group r2_mode : Int) : Prop := (shared_expr_Repair056_4 r1_group r1_mode r2_group r2_mode)

theorem propositional_1335 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ p2)))) ∨ p0 ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3228 (r1_group r1_mode r2_group r2_mode : Int) : (formula_1529 r1_group r1_mode r2_group r2_mode) := by
  exact (propositional_1335 ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair056_5 (r1_mode r2_mode : Int) : Prop := ((¬ ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))))
abbrev formula_1530 (r1_mode r2_mode : Int) : Prop := (shared_expr_Repair056_5 r1_mode r2_mode)

theorem propositional_1336 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3229 (r1_mode r2_mode : Int) : (formula_1530 r1_mode r2_mode) := by
  exact (propositional_1336 ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_3230 (c0_mode r1_mode r2_mode : Int) : ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ∨ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1337 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3231 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode) ∨ ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) := by
  exact (propositional_1337 ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair056_6 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) ∨ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∨ (¬ (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode)))
abbrev formula_1531 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair056_6 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)

theorem propositional_1338 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Prop) : ((¬ ((p0 ∧ ((¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((p3 ∧ (¬ p4)) ∨ ((¬ p3) ∧ (¬ p5)))))) ∨ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ ((p3 ∧ (¬ p8)) ∨ ((¬ p3) ∧ (¬ p5)))))) ∨ (¬ ((¬ p9) ∨ (¬ p10) ∨ (¬ ((p3 ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16)))) ∨ ((¬ p3) ∧ (¬ p4)))))) ∨ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ ((p3 ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p19) ∨ (¬ p15) ∨ (¬ p16)))) ∨ ((¬ p3) ∧ (¬ p4)))))) ∨ (¬ ((¬ p20) ∨ (¬ p21) ∨ (¬ ((p3 ∧ (¬ p8)) ∨ ((¬ p3) ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p22) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16)))))))) ∨ (¬ ((¬ p23) ∨ (¬ p24) ∨ (¬ ((p3 ∧ (¬ p8)) ∨ ((¬ p3) ∧ (¬ ((¬ p11) ∨ (¬ p12) ∨ (¬ p22) ∨ (¬ p19) ∨ (¬ p15) ∨ (¬ p16)))))))))) ∨ ((¬ p0) ∧ (¬ p25)))) ∨ p0 ∨ (¬ p25)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3232 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_1531 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) := by
  exact (propositional_1338 ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) (formula_877 c0_depth c0_kind c0_sign r1_level) ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) (r1_mode ≤ (1 : Int)) (r1_mode ≥ (1 : Int)) (formula_879 c0_depth c0_kind c0_sign r1_level) (r1_mode ≤ (2 : Int)) (r1_mode ≥ (2 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ((c0_node % (2 : Int)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) (r1_mode ≤ (3 : Int)) (r1_mode ≥ (3 : Int)) ((c0_node % (2 : Int)) ≥ (1 : Int)) (r1_mode ≤ (4 : Int)) (r1_mode ≥ (4 : Int)) ((¬ ((¬ (c0_sign ≤ (1 : Int))) ∨ (¬ (c0_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) (r1_mode ≤ (5 : Int)) (r1_mode ≥ (5 : Int)) (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode))

-- Checked replay of unit-resolution.
theorem replay_3233 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) : (¬ (formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode)) := by
  exact (Or.elim (replay_3232 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode) (fun l0 => (False.elim (l0 i193))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i12 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3234 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) : ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3231 c0_group c0_level c0_mode r1_group r1_level r1_mode) (fun l0 => (False.elim ((replay_3233 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193) l0))) (fun t0 => t0))

theorem propositional_1339 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3235 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : ((formula_38 c0_group c0_level c0_mode r2_group r2_level r2_mode) ∨ ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) := by
  exact (propositional_1339 ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3236 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : (¬ (formula_38 c0_group c0_level c0_mode r2_group r2_level r2_mode)) := by
  exact (Or.elim (replay_49 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode) (fun l0 => (False.elim (l0 i194))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i12 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3237 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3235 c0_group c0_level c0_mode r2_group r2_level r2_mode) (fun l0 => (False.elim ((replay_3236 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3238 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3230 c0_mode r1_mode r2_mode) (fun l0 => (False.elim (l0 (replay_3234 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3237 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194)))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_3239 (c0_mode r1_mode r2_mode : Int) : ((¬ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) ∨ (¬ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) ∨ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1340 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3240 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode) ∨ ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int))) := by
  exact (propositional_1340 ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3241 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) : ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3240 c0_group c0_level c0_mode r1_group r1_level r1_mode) (fun l0 => (False.elim ((replay_3233 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193) l0))) (fun t0 => t0))

theorem propositional_1341 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3242 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : ((formula_38 c0_group c0_level c0_mode r2_group r2_level r2_mode) ∨ ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int))) := by
  exact (propositional_1341 ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3243 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3242 c0_group c0_level c0_mode r2_group r2_level r2_mode) (fun l0 => (False.elim ((replay_3236 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3244 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3239 c0_mode r1_mode r2_mode) (fun l0 => (False.elim (l0 (replay_3241 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3243 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3245 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : (¬ ((¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r1_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_3229 r1_mode r2_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3238 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode i12 i193 i194)))) (fun t1 => (False.elim (t1 (replay_3244 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode i12 i193 i194)))))))

-- Checked replay of unit-resolution.
theorem replay_3246 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i195 : ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int))) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : (¬ (formula_596 r1_group r1_mode r2_group r2_mode)) := by
  exact (Or.elim (replay_3228 r1_group r1_mode r2_group r2_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3245 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode i12 i193 i194) l1))) (fun t1 => (False.elim (t1 i195))))))

abbrev shared_expr_Repair056_7 (r1_level r2_level : Int) : Prop := ((¬ ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int))))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int))))
abbrev formula_1532 (r1_level r2_level : Int) : Prop := (shared_expr_Repair056_7 r1_level r2_level)

theorem propositional_1342 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3247 (r1_level r2_level : Int) : (formula_1532 r1_level r2_level) := by
  exact (propositional_1342 ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_3248 (c0_level r1_level r2_level : Int) : ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1343 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3249 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode) ∨ ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  exact (propositional_1343 ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3250 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) : ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3249 c0_group c0_level c0_mode r1_group r1_level r1_mode) (fun l0 => (False.elim ((replay_3233 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193) l0))) (fun t0 => t0))

theorem propositional_1344 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3251 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : ((formula_38 c0_group c0_level c0_mode r2_group r2_level r2_mode) ∨ ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_1344 ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3252 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3251 c0_group c0_level c0_mode r2_group r2_level r2_mode) (fun l0 => (False.elim ((replay_3236 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3253 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3248 c0_level r1_level r2_level) (fun l0 => (False.elim (l0 (replay_3252 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3250 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193)))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_3254 (c0_level r1_level r2_level : Int) : ((¬ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1345 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3255 (c0_group c0_level c0_mode r1_group r1_level r1_mode : Int) : ((formula_890 c0_group c0_level c0_mode r1_group r1_level r1_mode) ∨ ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_1345 ((r1_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r1_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r1_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3256 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) : ((r1_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3255 c0_group c0_level c0_mode r1_group r1_level r1_mode) (fun l0 => (False.elim ((replay_3233 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193) l0))) (fun t0 => t0))

theorem propositional_1346 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3257 (c0_group c0_level c0_mode r2_group r2_level r2_mode : Int) : ((formula_38 c0_group c0_level c0_mode r2_group r2_level r2_mode) ∨ ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  exact (propositional_1346 ((r2_mode + ((-1 : Int) * c0_mode)) ≤ (0 : Int)) ((r2_mode + ((-1 : Int) * c0_mode)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≤ (0 : Int)) ((r2_group + ((-1 : Int) * c0_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3258 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r2_level + ((-1 : Int) * c0_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_3257 c0_group c0_level c0_mode r2_group r2_level r2_mode) (fun l0 => (False.elim ((replay_3236 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3259 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_3254 c0_level r1_level r2_level) (fun l0 => (False.elim (l0 (replay_3258 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode i12 i194)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3256 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode i12 i193)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_3260 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : (¬ ((¬ ((r1_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * r2_level)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_3247 r1_level r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3253 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode i12 i193 i194)))) (fun t1 => (False.elim (t1 (replay_3259 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode i12 i193 i194)))))))

-- Checked replay of unit-resolution.
theorem replay_3261 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) (i195 : ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int))) (i12 : (¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))))) (i196 : (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) (i193 : (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) (i194 : (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)) : False := by
  exact (Or.elim (replay_3227 r1_group r1_level r1_mode r2_group r2_level r2_mode) (fun l0 => (False.elim (l0 i196))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_3260 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode i12 i193 i194) l1))) (fun t1 => (False.elim ((replay_3246 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode i195 i12 i193 i194) t1))))))

abbrev shared_expr_Repair056_8 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∨ (¬ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ (¬ ((r1_group + ((-1 : Int) * r2_group)) ≥ (0 : Int))) ∨ (¬ (formula_891 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode)) ∨ (¬ (formula_52 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r2_group r2_level r2_mode)))
abbrev formula_1533 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair056_8 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode)

-- Checked replay of lemma.
theorem replay_3262 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : (formula_1533 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3261 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign r1_group r1_level r1_mode r2_group r2_level r2_mode (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr q)))))))

abbrev shared_expr_Repair056_9 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (¬ ((((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r1_mode ≥ (4 : Int)))))
abbrev formula_1534 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair056_9 r1_group r1_level r1_mode r2_group r2_level r2_mode)

theorem propositional_1347 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ p2))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3263 (r1_group r1_level r1_mode r2_group r2_level r2_mode : Int) : ((formula_1534 r1_group r1_level r1_mode r2_group r2_level r2_mode) ∨ (¬ ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∨ (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode)) := by
  exact (propositional_1347 ((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) (formula_597 r1_group r1_level r1_mode r2_group r2_level r2_mode) (r1_mode ≥ (4 : Int)))

theorem propositional_1348 (p0 p1 : Prop) : ((p0 ↔ p1) ∨ p0 ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3264 (r1_mode r2_mode : Int) : (((r1_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∨ (r1_mode ≥ (4 : Int)) ∨ (r2_mode ≥ (4 : Int))) := by
  exact (propositional_1348 (r1_mode ≥ (4 : Int)) (r2_mode ≥ (4 : Int)))

theorem propositional_1349 (p0 p1 : Prop) : ((¬ (p0 ↔ p1)) ∨ p0 ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3265 (r0_mode r1_mode : Int) : ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∨ (r0_mode ≥ (4 : Int)) ∨ (¬ (r1_mode ≥ (4 : Int)))) := by
  exact (propositional_1349 (r0_mode ≥ (4 : Int)) (r1_mode ≥ (4 : Int)))

abbrev shared_expr_Repair056_10 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (¬ ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))))
abbrev formula_1535 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair056_10 r0_group r0_level r0_mode r1_group r1_level r1_mode)

theorem propositional_1350 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ p2)) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ ((((¬ p3) ∨ (¬ p4)) ∧ (¬ p4)) ∨ ((¬ ((¬ p3) ∨ (¬ p4))) ∧ (¬ p5)))))) ∨ ((¬ p0) ∧ p6))) ∨ p0 ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3266 (r0_group r0_level r0_mode r1_group r1_level r1_mode : Int) : ((formula_1535 r0_group r0_level r0_mode r1_group r1_level r1_mode) ∨ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∨ (r0_mode ≥ (4 : Int))) := by
  exact (propositional_1350 ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)) ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)) (r0_mode ≥ (4 : Int)))

abbrev shared_expr_Repair056_11 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := ((¬ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) ∨ (¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))) ∨ ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))))
abbrev formula_1536 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : Prop := (shared_expr_Repair056_11 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)

theorem propositional_1351 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ p2)) ∨ (¬ p0) ∨ (¬ p1) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3267 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : (formula_1536 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := by
  exact (propositional_1351 (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))))

theorem propositional_1352 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3268 (r1_kind : Int) : (((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) ∨ (r1_kind ≥ (0 : Int))) := by
  exact (propositional_1352 (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3269 (r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i197 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : (formula_595 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_697 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim (i197 t0))))

-- Checked replay of unit-resolution.
theorem replay_3270 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i197 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) := by
  exact (Or.elim (replay_726 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_3269 r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i197)))))

-- Checked replay of unit-resolution.
theorem replay_3271 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i197 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : (r1_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_3268 r1_kind) (fun l0 => (False.elim ((replay_3270 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 i197) l0))) (fun t0 => t0))

abbrev shared_expr_Repair056_12 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) ∨ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ∨ (¬ (formula_524 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))
abbrev formula_1537 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair056_12 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem propositional_1353 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : (p0 ∨ p1 ∨ (¬ ((p0 ∧ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ ((((¬ p8) ∨ (¬ p9)) ∧ ((((¬ p10) ∨ (¬ p11)) ∧ ((¬ p12) ∨ (¬ p13) ∨ ((((¬ p14) ∨ (¬ p15)) ∧ (¬ p14)) ∨ ((¬ ((¬ p14) ∨ (¬ p15))) ∧ (¬ ((¬ p16) ∨ (¬ p17))))))) ∨ ((¬ ((¬ p10) ∨ (¬ p11))) ∧ ((((¬ p18) ∨ (¬ p19)) ∧ (¬ p19)) ∨ ((¬ ((¬ p18) ∨ (¬ p19))) ∧ (¬ ((¬ p20) ∨ (¬ p21)))))))) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ ((((¬ p22) ∨ (¬ p23)) ∧ (¬ p23)) ∨ ((¬ ((¬ p22) ∨ (¬ p23))) ∧ (¬ ((¬ p21) ∨ (¬ p17) ∨ (¬ p16) ∨ (¬ p20)))))))))))) ∨ ((¬ p0) ∧ p1)))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3272 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_1537 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (propositional_1353 ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (r0_kind ≤ (2 : Int)) (r0_kind ≥ (2 : Int)) (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (-1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≤ (1 : Int)) ((r0_depth + ((-1 : Int) * r1_depth)) ≥ (1 : Int)) ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((r0_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) (r0_sign ≤ (1 : Int)) (r0_sign ≥ (1 : Int)) ((r0_node + ((-1 : Int) * r1_node)) ≤ (0 : Int)) ((r0_node + ((-1 : Int) * r1_node)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3273 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) ∨ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode)) := by
  exact (Or.elim (replay_3272 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl (Or.inl l100))) (fun t100 => (Or.inl (Or.inr t100))))) (fun t0 => (Or.elim t0 (fun l1 => (Or.elim l1 (fun l100 => (Or.inr (Or.inl l100))) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inr (Or.inl l101)))) (fun t101 => (Or.inr (Or.inr (Or.inr t101)))))))) (fun t1 => (False.elim (t1 (replay_530 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33)))))))

-- Checked replay of unit-resolution.
theorem replay_3274 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i198 : (¬ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))) : ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_3273 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i198 t0))))

-- Checked replay of unit-resolution.
theorem replay_3275 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i198 : (¬ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))) : (¬ (formula_520 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign)) := by
  exact (Or.elim (replay_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33) (fun l0 => (False.elim (l0 (replay_3274 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33 i198)))) (fun t0 => t0))

theorem propositional_1354 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (((p2 ↔ p3) ∧ ((((¬ p4) ∨ (¬ p5)) ∧ (¬ p5)) ∨ ((¬ ((¬ p4) ∨ (¬ p5))) ∧ ((((¬ p6) ∨ (¬ p7)) ∧ (¬ p7)) ∨ ((¬ ((¬ p6) ∨ (¬ p7))) ∧ (¬ p8)))))) ∨ ((¬ (p2 ↔ p3)) ∧ p2))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3276 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ∨ (r1_kind ≥ (0 : Int))) := by
  exact (propositional_1354 (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) (r0_mode ≥ (4 : Int)) (r1_mode ≥ (4 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)) ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3277 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) (i198 : (¬ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))) : (r1_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_3276 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (fun l0 => (False.elim (i198 l0))) (fun t0 => t0))

theorem propositional_1355 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (((p2 ↔ p3) ∧ ((((¬ p4) ∨ (¬ p5)) ∧ (¬ p5)) ∨ ((¬ ((¬ p4) ∨ (¬ p5))) ∧ ((((¬ p6) ∨ (¬ p7)) ∧ (¬ p7)) ∨ ((¬ ((¬ p6) ∨ (¬ p7))) ∧ (¬ p8)))))) ∨ ((¬ (p2 ↔ p3)) ∧ p2))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3278 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) : ((formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) ∨ (r1_kind ≤ (0 : Int))) := by
  exact (propositional_1355 (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) (r0_mode ≥ (4 : Int)) (r1_mode ≥ (4 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≤ (0 : Int)) ((r0_level + ((-1 : Int) * r1_level)) ≥ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * r1_mode)) ≥ (0 : Int)) ((r0_group + ((-1 : Int) * r1_group)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_3279 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) (i198 : (¬ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))) : (r1_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_3278 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (fun l0 => (False.elim (i198 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3280 (r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode : Int) (i198 : (¬ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))) : (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) := by
  exact (Or.elim (replay_2099 r1_kind) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3279 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode i198)))) (fun t1 => (False.elim (t1 (replay_3277 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode i198)))))))

-- Checked replay of unit-resolution.
theorem replay_3281 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i198 : (¬ (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode))) : False := by
  exact (Or.elim (replay_532 r0_depth r0_kind r0_node r0_sign r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_3275 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33 i198) l0))) (fun t0 => (False.elim ((replay_3280 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode i198) t0))))

-- Checked replay of lemma.
theorem replay_3282 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_523 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_3281 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33 (by
    exact nc))

-- Checked replay of unit-resolution.
theorem replay_3283 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i197 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : (r1_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_727 r1_kind) (fun l0 => (False.elim ((replay_3270 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 i197) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_3284 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i197 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) : ((((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) ∧ (formula_522 r0_group r0_level r0_mode r1_group r1_level r1_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int)))) := by
  exact (Or.elim (replay_3267 r0_group r0_level r0_mode r1_group r1_kind r1_level r1_mode) (fun l0 => (False.elim (l0 (replay_3282 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i33)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_3283 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 i197)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_3271 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62 i197)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_3285 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i197 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) (i199 : (¬ (r0_mode ≥ (4 : Int)))) : ((r0_mode ≥ (4 : Int)) ↔ (r1_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_3266 r0_group r0_level r0_mode r1_group r1_level r1_mode) (fun l0 => (False.elim (l0 (replay_3284 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i33 i62 i197)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (i199 t1))))))

-- Checked replay of unit-resolution.
theorem replay_3286 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i197 : (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int)))))) (i199 : (¬ (r0_mode ≥ (4 : Int)))) : (¬ (r1_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_3265 r0_mode r1_mode) (fun l0 => (False.elim (l0 (replay_3285 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i33 i62 i197 i199)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i199 l1))) (fun t1 => t1))))

theorem propositional_1356 (p0 p1 : Prop) : ((¬ (p0 ↔ p1)) ∨ p0 ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3287 (r0_mode r2_mode : Int) : ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∨ (r0_mode ≥ (4 : Int)) ∨ (¬ (r2_mode ≥ (4 : Int)))) := by
  exact (propositional_1356 (r0_mode ≥ (4 : Int)) (r2_mode ≥ (4 : Int)))

abbrev shared_expr_Repair056_13 (r0_group r0_mode r2_group r2_mode : Int) : Prop := ((((¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int))) ∨ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int))))) ∧ (¬ ((r0_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)))))
abbrev formula_1538 (r0_group r0_mode r2_group r2_mode : Int) : Prop := (shared_expr_Repair056_13 r0_group r0_mode r2_group r2_mode)

abbrev shared_expr_Repair056_14 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int))) ∨ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≥ (0 : Int))))) ∧ (formula_1538 r0_group r0_mode r2_group r2_mode)))
abbrev formula_1539 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Repair056_14 r0_group r0_level r0_mode r2_group r2_level r2_mode)

abbrev shared_expr_Repair056_15 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := ((((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (formula_1539 r0_group r0_level r0_mode r2_group r2_level r2_mode)) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int))))
abbrev formula_1540 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := (¬ (shared_expr_Repair056_15 r0_group r0_level r0_mode r2_group r2_level r2_mode))

theorem propositional_1357 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ p2)) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ ((((¬ p3) ∨ (¬ p4)) ∧ (¬ p4)) ∨ ((¬ ((¬ p3) ∨ (¬ p4))) ∧ (¬ p5)))))) ∨ ((¬ p0) ∧ p6))) ∨ p0 ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3288 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : ((formula_1540 r0_group r0_level r0_mode r2_group r2_level r2_mode) ∨ ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∨ (r0_mode ≥ (4 : Int))) := by
  exact (propositional_1357 ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ((r0_level + ((-1 : Int) * r2_level)) ≥ (0 : Int)) ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ((r0_mode + ((-1 : Int) * r2_mode)) ≥ (0 : Int)) ((r0_group + ((-1 : Int) * r2_group)) ≥ (0 : Int)) (r0_mode ≥ (4 : Int)))

abbrev formula_1541 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))) ∨ (shared_expr_Repair056_15 r0_group r0_level r0_mode r2_group r2_level r2_mode))

abbrev shared_expr_Repair056_16 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((¬ (formula_1541 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode)) ∨ (¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))) ∨ (shared_expr_Repair056_15 r0_group r0_level r0_mode r2_group r2_level r2_mode))
abbrev formula_1542 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (shared_expr_Repair056_16 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode)

theorem propositional_1358 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ p2)) ∨ (¬ p0) ∨ (¬ p1) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3289 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : (formula_1542 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode) := by
  exact (propositional_1358 (r2_kind ≤ (0 : Int)) (r2_kind ≥ (0 : Int)) (shared_expr_Repair056_15 r0_group r0_level r0_mode r2_group r2_level r2_mode))

abbrev formula_1543 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((¬ (formula_1541 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode)) ∨ (¬ (r2_kind ≤ (0 : Int))) ∨ (shared_expr_Repair056_15 r0_group r0_level r0_mode r2_group r2_level r2_mode))

-- Checked replay of unit-resolution.
theorem replay_3290 (h r0_group r0_level r0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_1543 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode) := by
  exact (Or.elim (replay_3289 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr (Or.inl l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_137 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i10)))) (fun t2 => (Or.inr (Or.inr t2))))))))

abbrev shared_expr_Repair056_17 (r0_node r2_node : Int) : Prop := (((¬ ((r2_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((r2_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Repair056_18 (r0_node r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))))
abbrev formula_1544 (r0_node r2_node r2_sign : Int) : Prop := ((shared_expr_Repair056_17 r0_node r2_node) ∨ (shared_expr_Repair056_18 r0_node r2_node r2_sign))

abbrev shared_expr_Repair056_19 (r0_node r2_node : Int) : Prop := (((¬ ((r0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((r0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Repair056_20 (r0_node r0_sign r2_node : Int) : Prop := ((¬ ((¬ ((r0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r0_sign ≥ (1 : Int))))))
abbrev formula_1545 (r0_node r0_sign r2_node : Int) : Prop := ((shared_expr_Repair056_19 r0_node r2_node) ∨ (shared_expr_Repair056_20 r0_node r0_sign r2_node))

abbrev shared_expr_Repair056_21 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : Prop := (((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_1544 r0_node r2_node r2_sign)))
abbrev shared_expr_Repair056_22 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := ((shared_expr_Repair056_21 r0_depth r0_node r2_depth r2_node r2_sign) ∨ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int))))) ∧ (formula_1545 r0_node r0_sign r2_node)))
abbrev formula_1546 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_22 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair056_23 (r0_node r0_sign r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (r0_sign ≥ (1 : Int))) ∨ (¬ (r0_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))))
abbrev shared_expr_Repair056_24 (r0_node r0_sign r2_node r2_sign : Int) : Prop := ((((¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∨ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) ∧ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))) ∨ (shared_expr_Repair056_23 r0_node r0_sign r2_node r2_sign))
abbrev formula_1547 (r0_node r0_sign r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_24 r0_node r0_sign r2_node r2_sign)

abbrev shared_expr_Repair056_25 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)))) ∧ (formula_1546 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)) ∨ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) ∧ (formula_1547 r0_node r0_sign r2_node r2_sign)))
abbrev formula_1548 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_25 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair056_26 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (r2_kind ≤ (0 : Int))) ∨ (¬ (r2_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (formula_1548 r0_depth r0_node r0_sign r2_depth r2_node r2_sign))))
abbrev formula_1549 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_26 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair056_27 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) ∧ (¬ (formula_1549 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign))) ∨ ((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∧ (formula_1541 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode)))
abbrev formula_1550 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_27 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair056_28 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) ∨ (formula_1541 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode) ∨ (¬ (formula_1550 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)))
abbrev formula_1551 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_28 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem propositional_1359 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : (p0 ∨ p1 ∨ (¬ ((p0 ∧ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ ((((¬ p8) ∨ (¬ p9)) ∧ ((((¬ p10) ∨ (¬ p11)) ∧ ((¬ p12) ∨ (¬ p13) ∨ ((((¬ p14) ∨ (¬ p15)) ∧ (¬ p14)) ∨ ((¬ ((¬ p14) ∨ (¬ p15))) ∧ (¬ ((¬ p16) ∨ (¬ p17))))))) ∨ ((¬ ((¬ p10) ∨ (¬ p11))) ∧ ((((¬ p18) ∨ (¬ p19)) ∧ (¬ p19)) ∨ ((¬ ((¬ p18) ∨ (¬ p19))) ∧ (¬ ((¬ p20) ∨ (¬ p21)))))))) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ ((((¬ p22) ∨ (¬ p23)) ∧ (¬ p23)) ∨ ((¬ ((¬ p22) ∨ (¬ p23))) ∧ (¬ ((¬ p21) ∨ (¬ p20) ∨ (¬ p16) ∨ (¬ p17)))))))))))) ∨ ((¬ p0) ∧ p1)))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_3291 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1551 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (propositional_1359 ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) (formula_1541 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode) (r0_kind ≤ (2 : Int)) (r0_kind ≥ (2 : Int)) (r2_kind ≤ (0 : Int)) (r2_kind ≥ (0 : Int)) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (-1 : Int)) ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)) ((r0_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int)) ((r2_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * (r0_node / (2 : Int)))) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) ((r0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ((r0_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) (r0_sign ≤ (1 : Int)) (r0_sign ≥ (1 : Int)) ((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ((r0_node + ((-1 : Int) * r2_node)) ≥ (0 : Int)))

abbrev shared_expr_Repair056_29 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := ((¬ (¬ ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))))) ∧ (((r0_level ≠ r2_level) ∧ (r0_level < r2_level)) ∨ ((¬ (r0_level ≠ r2_level)) ∧ (((r0_mode ≠ r2_mode) ∧ (r0_mode < r2_mode)) ∨ ((¬ (r0_mode ≠ r2_mode)) ∧ (r0_group < r2_group))))))
abbrev formula_1552 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int))) ∨ (shared_expr_Repair056_29 r0_group r0_level r0_mode r2_group r2_level r2_mode))

abbrev shared_expr_Repair056_30 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : Prop := ((((r2_depth + (1 : Int)) = r0_depth) ∧ (((r2_node = (r0_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r0_node / (2 : Int)))) ∧ ((r0_node / (2 : Int)) < r2_node)))) ∨ ((¬ ((r2_depth + (1 : Int)) = r0_depth)) ∧ True))
abbrev formula_1553 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_30 r0_depth r0_node r2_depth r2_node r2_sign)

abbrev shared_expr_Repair056_31 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := ((((r0_depth + (1 : Int)) = r2_depth) ∧ (((r0_node = (r2_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r2_node / (2 : Int)))) ∧ (r0_node < (r2_node / (2 : Int)))))) ∨ ((¬ ((r0_depth + (1 : Int)) = r2_depth)) ∧ (formula_1553 r0_depth r0_node r2_depth r2_node r2_sign)))
abbrev formula_1554 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_31 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair056_32 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (((r0_depth = r2_depth) ∧ (((r0_node = r2_node) ∧ ((r0_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r0_node = r2_node)) ∧ (r0_node < r2_node)))) ∨ ((¬ (r0_depth = r2_depth)) ∧ (formula_1554 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))
abbrev formula_1555 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_32 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair056_33 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((r0_kind = (2 : Int)) ∧ (False ∧ (r2_kind = (1 : Int)))) ∨ ((¬ (r0_kind = (2 : Int))) ∧ (((r2_kind = (2 : Int)) ∧ True) ∨ ((¬ (r2_kind = (2 : Int))) ∧ (formula_1555 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))))
abbrev formula_1556 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_33 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair056_34 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((r0_kind = (0 : Int)) ∧ (((r2_kind = (0 : Int)) ∧ (formula_1552 r0_group r0_level r0_mode r2_group r2_level r2_mode)) ∨ ((¬ (r2_kind = (0 : Int))) ∧ True))) ∨ ((¬ (r0_kind = (0 : Int))) ∧ (((r2_kind = (0 : Int)) ∧ False) ∨ ((¬ (r2_kind = (0 : Int))) ∧ (formula_1556 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))))
abbrev formula_1557 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_34 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair056_35 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := (((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ∧ (((r0_level = r2_level) ∧ (((r0_mode = r2_mode) ∧ (¬ (r2_group ≤ r0_group))) ∨ ((¬ (r0_mode = r2_mode)) ∧ (¬ (r2_mode ≤ r0_mode))))) ∨ ((¬ (r0_level = r2_level)) ∧ (¬ (r2_level ≤ r0_level)))))
abbrev formula_1558 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := ((shared_expr_Repair056_35 r0_group r0_level r0_mode r2_group r2_level r2_mode) ∨ ((¬ ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ∧ (r0_mode ≥ (4 : Int))))

abbrev shared_expr_Repair056_36 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : Prop := ((¬ (r0_depth = ((-1 : Int) + r2_depth))) ∧ ((¬ (r2_depth = ((-1 : Int) + r0_depth))) ∨ (((r2_node = (r0_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r0_node / (2 : Int)))) ∧ (¬ (r2_node ≤ (r0_node / (2 : Int))))))))
abbrev shared_expr_Repair056_37 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (((r0_depth = ((-1 : Int) + r2_depth)) ∧ (((r0_node = (r2_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r2_node / (2 : Int)))) ∧ (¬ ((r2_node / (2 : Int)) ≤ r0_node))))) ∨ (shared_expr_Repair056_36 r0_depth r0_node r2_depth r2_node r2_sign))
abbrev formula_1559 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_37 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair056_38 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (((r0_depth = r2_depth) ∧ (((r0_node = r2_node) ∧ ((r0_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r0_node = r2_node)) ∧ (¬ (r2_node ≤ r0_node))))) ∨ ((¬ (r0_depth = r2_depth)) ∧ (formula_1559 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))
abbrev formula_1560 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_38 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair056_39 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((r0_kind = (0 : Int)) ∧ ((¬ (r2_kind = (0 : Int))) ∨ (formula_1558 r0_group r0_level r0_mode r2_group r2_level r2_mode))) ∨ ((¬ (r0_kind = (0 : Int))) ∧ ((¬ (r2_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_1560 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))))
abbrev formula_1561 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_39 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

abbrev shared_expr_Repair056_40 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((formula_1557 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (formula_1561 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
abbrev formula_1562 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (shared_expr_Repair056_40 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)

theorem normalized_1360 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (False ∧ (p10 ∧ (¬ p11)))) ∨ ((¬ p9) ∧ ((p12 ∧ True) ∨ ((¬ p12) ∧ ((p13 ∧ ((p14 ∧ p15) ∨ ((¬ p14) ∧ p16))) ∨ ((¬ p13) ∧ ((p17 ∧ p18) ∨ ((¬ p17) ∧ ((p19 ∧ ((p20 ∧ p21) ∨ ((¬ p20) ∧ p22))) ∨ ((¬ p19) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ (¬ p9) ∧ (p12 ∨ ((p13 ∧ ((p14 ∧ p15) ∨ ((¬ p14) ∧ (¬ (¬ p16))))) ∨ ((¬ p13) ∧ ((p17 ∧ p18) ∨ ((¬ p17) ∧ ((¬ p19) ∨ ((p20 ∧ p21) ∨ ((¬ p20) ∧ (¬ (¬ p22)))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5362 (r0_mode r2_mode : Int) : (¬ ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_1963 r0_mode) (normalization_534 r2_mode)))

theorem normalization_5363 (r0_level r2_level : Int) : (r0_level ≠ r2_level) ↔ (¬ (((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_5364 (r0_level r2_level : Int) : (r0_level < r2_level) ↔ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5365 (r0_mode r2_mode : Int) : (r0_mode ≠ r2_mode) ↔ (¬ (((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_5366 (r0_mode r2_mode : Int) : (r0_mode < r2_mode) ↔ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_5367 (r0_group r2_group : Int) : (r0_group < r2_group) ↔ ((r0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair056_41 (r0_group r0_mode r2_group r2_mode : Int) : Prop := (((¬ (((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) ∧ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))))) ∧ ((r0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))))
theorem normalization_5368 (r0_group r0_mode r2_group r2_mode : Int) : (((r0_mode ≠ r2_mode) ∧ (r0_mode < r2_mode)) ∨ ((¬ (r0_mode ≠ r2_mode)) ∧ (r0_group < r2_group))) ↔ (shared_expr_Repair056_41 r0_group r0_mode r2_group r2_mode) := (or_congr (and_congr (normalization_5365 r0_mode r2_mode) (normalization_5366 r0_mode r2_mode)) (and_congr (not_congr (normalization_5365 r0_mode r2_mode)) (normalization_5367 r0_group r2_group)))

abbrev shared_expr_Repair056_42 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ (((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) ∧ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair056_41 r0_group r0_mode r2_group r2_mode)))
theorem normalization_5369 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : (((r0_level ≠ r2_level) ∧ (r0_level < r2_level)) ∨ ((¬ (r0_level ≠ r2_level)) ∧ (((r0_mode ≠ r2_mode) ∧ (r0_mode < r2_mode)) ∨ ((¬ (r0_mode ≠ r2_mode)) ∧ (r0_group < r2_group))))) ↔ (shared_expr_Repair056_42 r0_group r0_level r0_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_5363 r0_level r2_level) (normalization_5364 r0_level r2_level)) (and_congr (not_congr (normalization_5363 r0_level r2_level)) (normalization_5368 r0_group r0_mode r2_group r2_mode)))

abbrev shared_expr_Repair056_43 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) ∧ (¬ ((r0_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair056_42 r0_group r0_level r0_mode r2_group r2_level r2_mode)))
theorem normalization_5370 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : (formula_1552 r0_group r0_level r0_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair056_43 r0_group r0_level r0_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_5362 r0_mode r2_mode) (normalization_1963 r0_mode)) (and_congr (not_congr (normalization_5362 r0_mode r2_mode)) (normalization_5369 r0_group r0_level r0_mode r2_group r2_level r2_mode)))

abbrev shared_expr_Repair056_44 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := (((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair056_43 r0_group r0_level r0_mode r2_group r2_level r2_mode)) ∨ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_5371 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : (((r2_kind = (0 : Int)) ∧ (formula_1552 r0_group r0_level r0_mode r2_group r2_level r2_mode)) ∨ ((¬ (r2_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Repair056_44 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode) := (or_congr (and_congr (normalization_133 r2_kind) (normalization_5370 r0_group r0_level r0_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_133 r2_kind)) (normalization_305)))

theorem normalization_5372 (r0_depth r2_depth : Int) : (r0_depth = r2_depth) ↔ (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5373 (r0_node r2_node : Int) : (r0_node = r2_node) ↔ (((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5374 (r0_sign r2_sign : Int) : ((r0_sign = (1 : Int)) ∧ (r2_sign = (0 : Int))) ↔ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) := (and_congr (normalization_1497 r0_sign) (normalization_183 r2_sign))

theorem normalization_5375 (r0_node r2_node : Int) : (r0_node < r2_node) ↔ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair056_45 (r0_node r0_sign r2_node r2_sign : Int) : Prop := ((((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ∧ ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))))
abbrev shared_expr_Repair056_46 (r0_node r0_sign r2_node r2_sign : Int) : Prop := ((shared_expr_Repair056_45 r0_node r0_sign r2_node r2_sign) ∨ ((¬ (((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) ∧ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))
theorem normalization_5376 (r0_node r0_sign r2_node r2_sign : Int) : (((r0_node = r2_node) ∧ ((r0_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r0_node = r2_node)) ∧ (r0_node < r2_node))) ↔ (shared_expr_Repair056_46 r0_node r0_sign r2_node r2_sign) := (or_congr (and_congr (normalization_5373 r0_node r2_node) (normalization_5374 r0_sign r2_sign)) (and_congr (not_congr (normalization_5373 r0_node r2_node)) (normalization_5375 r0_node r2_node)))

theorem normalization_5377 (r0_depth r2_depth : Int) : ((r0_depth + (1 : Int)) = r2_depth) ↔ (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_5378 (r0_node r2_node : Int) : (r0_node = (r2_node / (2 : Int))) ↔ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_5379 (r0_node r2_node : Int) : (r0_node < (r2_node / (2 : Int))) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Repair056_47 (r0_node r2_node : Int) : Prop := ((¬ ((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)))) ∧ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair056_48 (r0_node r0_sign r2_node : Int) : Prop := ((((¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (-1 : Int))) ∧ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) ∧ (((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair056_47 r0_node r2_node))
theorem normalization_5380 (r0_node r0_sign r2_node : Int) : (((r0_node = (r2_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r2_node / (2 : Int)))) ∧ (r0_node < (r2_node / (2 : Int))))) ↔ (shared_expr_Repair056_48 r0_node r0_sign r2_node) := (or_congr (and_congr (normalization_5378 r0_node r2_node) (normalization_1497 r0_sign)) (and_congr (not_congr (normalization_5378 r0_node r2_node)) (normalization_5379 r0_node r2_node)))

theorem normalization_5381 (r0_depth r2_depth : Int) : ((r2_depth + (1 : Int)) = r0_depth) ↔ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_5382 (r0_node r2_node : Int) : (r2_node = (r0_node / (2 : Int))) ↔ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_5383 (r0_node r2_node : Int) : ((r0_node / (2 : Int)) < r2_node) ↔ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair056_49 (r0_node r2_node : Int) : Prop := ((¬ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair056_50 (r0_node r2_node r2_sign : Int) : Prop := ((((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair056_49 r0_node r2_node))
theorem normalization_5384 (r0_node r2_node r2_sign : Int) : (((r2_node = (r0_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r0_node / (2 : Int)))) ∧ ((r0_node / (2 : Int)) < r2_node))) ↔ (shared_expr_Repair056_50 r0_node r2_node r2_sign) := (or_congr (and_congr (normalization_5382 r0_node r2_node) (normalization_183 r2_sign)) (and_congr (not_congr (normalization_5382 r0_node r2_node)) (normalization_5383 r0_node r2_node)))

abbrev shared_expr_Repair056_51 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : Prop := ((((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∧ (shared_expr_Repair056_50 r0_node r2_node r2_sign)) ∨ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_5385 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : (formula_1553 r0_depth r0_node r2_depth r2_node r2_sign) ↔ (shared_expr_Repair056_51 r0_depth r0_node r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_5381 r0_depth r2_depth) (normalization_5384 r0_node r2_node r2_sign)) (and_congr (not_congr (normalization_5381 r0_depth r2_depth)) (normalization_305)))

abbrev shared_expr_Repair056_52 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair056_48 r0_node r0_sign r2_node)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair056_51 r0_depth r0_node r2_depth r2_node r2_sign)))
theorem normalization_5386 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : (formula_1554 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair056_52 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_5377 r0_depth r2_depth) (normalization_5380 r0_node r0_sign r2_node)) (and_congr (not_congr (normalization_5377 r0_depth r2_depth)) (normalization_5385 r0_depth r0_node r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair056_53 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair056_46 r0_node r0_sign r2_node r2_sign)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair056_52 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))
theorem normalization_5387 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : (formula_1555 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair056_53 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_5372 r0_depth r2_depth) (normalization_5376 r0_node r0_sign r2_node r2_sign)) (and_congr (not_congr (normalization_5372 r0_depth r2_depth)) (normalization_5386 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair056_54 (r0_depth r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∧ True) ∨ ((¬ (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair056_53 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))
theorem normalization_5388 (r0_depth r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : (((r2_kind = (2 : Int)) ∧ True) ∨ ((¬ (r2_kind = (2 : Int))) ∧ (formula_1555 r0_depth r0_node r0_sign r2_depth r2_node r2_sign))) ↔ (shared_expr_Repair056_54 r0_depth r0_node r0_sign r2_depth r2_kind r2_node r2_sign) := (or_congr (and_congr (normalization_201 r2_kind) (normalization_305)) (and_congr (not_congr (normalization_201 r2_kind)) (normalization_5387 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair056_55 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ∧ (False ∧ (((r2_kind) ≤ (1 : Int)) ∧ (¬ ((r2_kind) ≤ (0 : Int)))))) ∨ ((¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair056_54 r0_depth r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_5389 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_1556 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign) ↔ (shared_expr_Repair056_55 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign) := (or_congr (and_congr (normalization_1506 r0_kind) (normalization_2476 r2_kind)) (and_congr (not_congr (normalization_1506 r0_kind)) (normalization_5388 r0_depth r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair056_56 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair056_55 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_5390 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : (((r2_kind = (0 : Int)) ∧ False) ∨ ((¬ (r2_kind = (0 : Int))) ∧ (formula_1556 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign))) ↔ (shared_expr_Repair056_56 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign) := (or_congr (and_congr (normalization_133 r2_kind) (normalization_1253)) (and_congr (not_congr (normalization_133 r2_kind)) (normalization_5389 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair056_57 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := (((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair056_44 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode)) ∨ ((¬ (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair056_56 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_5391 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1557 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair056_57 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_1438 r0_kind) (normalization_5371 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode)) (and_congr (not_congr (normalization_1438 r0_kind)) (normalization_5390 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))

theorem normalization_5392 (r0_mode r2_mode : Int) : ((r0_mode ≥ (4 : Int)) ↔ (r2_mode ≥ (4 : Int))) ↔ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))) := (iff_congr (normalization_1963 r0_mode) (normalization_534 r2_mode))

theorem normalization_5393 (r0_level r2_level : Int) : (r0_level = r2_level) ↔ (((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5394 (r0_mode r2_mode : Int) : (r0_mode = r2_mode) ↔ (((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_5395 (r0_group r2_group : Int) : (r2_group ≤ r0_group) ↔ (¬ ((r0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5396 (r0_group r2_group : Int) : (¬ (r2_group ≤ r0_group)) ↔ (¬ (¬ ((r0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)))) := (not_congr (normalization_5395 r0_group r2_group))

theorem normalization_5397 (r0_mode r2_mode : Int) : (r2_mode ≤ r0_mode) ↔ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5398 (r0_mode r2_mode : Int) : (¬ (r2_mode ≤ r0_mode)) ↔ (¬ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_5397 r0_mode r2_mode))

abbrev shared_expr_Repair056_58 (r0_group r0_mode r2_group r2_mode : Int) : Prop := (((((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((r0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int))))) ∨ ((¬ (((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int))))))
theorem normalization_5399 (r0_group r0_mode r2_group r2_mode : Int) : (((r0_mode = r2_mode) ∧ (¬ (r2_group ≤ r0_group))) ∨ ((¬ (r0_mode = r2_mode)) ∧ (¬ (r2_mode ≤ r0_mode)))) ↔ (shared_expr_Repair056_58 r0_group r0_mode r2_group r2_mode) := (or_congr (and_congr (normalization_5394 r0_mode r2_mode) (normalization_5396 r0_group r2_group)) (and_congr (not_congr (normalization_5394 r0_mode r2_mode)) (normalization_5398 r0_mode r2_mode)))

theorem normalization_5400 (r0_level r2_level : Int) : (r2_level ≤ r0_level) ↔ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5401 (r0_level r2_level : Int) : (¬ (r2_level ≤ r0_level)) ↔ (¬ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) := (not_congr (normalization_5400 r0_level r2_level))

abbrev shared_expr_Repair056_59 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := (((((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair056_58 r0_group r0_mode r2_group r2_mode)) ∨ ((¬ (((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int))))))
theorem normalization_5402 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : (((r0_level = r2_level) ∧ (((r0_mode = r2_mode) ∧ (¬ (r2_group ≤ r0_group))) ∨ ((¬ (r0_mode = r2_mode)) ∧ (¬ (r2_mode ≤ r0_mode))))) ∨ ((¬ (r0_level = r2_level)) ∧ (¬ (r2_level ≤ r0_level)))) ↔ (shared_expr_Repair056_59 r0_group r0_level r0_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_5393 r0_level r2_level) (normalization_5399 r0_group r0_mode r2_group r2_mode)) (and_congr (not_congr (normalization_5393 r0_level r2_level)) (normalization_5401 r0_level r2_level)))

abbrev shared_expr_Repair056_60 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : Prop := ((((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair056_59 r0_group r0_level r0_mode r2_group r2_level r2_mode)) ∨ ((¬ ((¬ ((r0_mode) ≤ (3 : Int))) ↔ (¬ ((r2_mode) ≤ (3 : Int))))) ∧ (¬ ((r0_mode) ≤ (3 : Int)))))
theorem normalization_5403 (r0_group r0_level r0_mode r2_group r2_level r2_mode : Int) : (formula_1558 r0_group r0_level r0_mode r2_group r2_level r2_mode) ↔ (shared_expr_Repair056_60 r0_group r0_level r0_mode r2_group r2_level r2_mode) := (or_congr (and_congr (normalization_5392 r0_mode r2_mode) (normalization_5402 r0_group r0_level r0_mode r2_group r2_level r2_mode)) (and_congr (not_congr (normalization_5392 r0_mode r2_mode)) (normalization_1963 r0_mode)))

theorem normalization_5404 (r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : ((¬ (r2_kind = (0 : Int))) ∨ (formula_1558 r0_group r0_level r0_mode r2_group r2_level r2_mode)) ↔ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair056_60 r0_group r0_level r0_mode r2_group r2_level r2_mode)) := (or_congr (normalization_2498 r2_kind) (normalization_5403 r0_group r0_level r0_mode r2_group r2_level r2_mode))

theorem normalization_5405 (r0_node r2_node : Int) : (r2_node ≤ r0_node) ↔ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5406 (r0_node r2_node : Int) : (¬ (r2_node ≤ r0_node)) ↔ (¬ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5405 r0_node r2_node))

abbrev shared_expr_Repair056_61 (r0_node r0_sign r2_node r2_sign : Int) : Prop := ((shared_expr_Repair056_45 r0_node r0_sign r2_node r2_sign) ∨ ((¬ (((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int))))))
theorem normalization_5407 (r0_node r0_sign r2_node r2_sign : Int) : (((r0_node = r2_node) ∧ ((r0_sign = (1 : Int)) ∧ (r2_sign = (0 : Int)))) ∨ ((¬ (r0_node = r2_node)) ∧ (¬ (r2_node ≤ r0_node)))) ↔ (shared_expr_Repair056_61 r0_node r0_sign r2_node r2_sign) := (or_congr (and_congr (normalization_5373 r0_node r2_node) (normalization_5374 r0_sign r2_sign)) (and_congr (not_congr (normalization_5373 r0_node r2_node)) (normalization_5406 r0_node r2_node)))

theorem normalization_5408 (r0_depth r2_depth : Int) : (r0_depth = ((-1 : Int) + r2_depth)) ↔ (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_5409 (r0_node r2_node : Int) : ((r2_node / (2 : Int)) ≤ r0_node) ↔ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5410 (r0_node r2_node : Int) : (¬ ((r2_node / (2 : Int)) ≤ r0_node)) ↔ (¬ (((r2_node / (2 : Int)) + ((-1 : Int) * r0_node)) ≤ (0 : Int))) := (not_congr (normalization_5409 r0_node r2_node))

theorem normalization_5411 (r0_node r0_sign r2_node : Int) : (((r0_node = (r2_node / (2 : Int))) ∧ (r0_sign = (1 : Int))) ∨ ((¬ (r0_node = (r2_node / (2 : Int)))) ∧ (¬ ((r2_node / (2 : Int)) ≤ r0_node)))) ↔ (shared_expr_Repair056_48 r0_node r0_sign r2_node) := (or_congr (and_congr (normalization_5378 r0_node r2_node) (normalization_1497 r0_sign)) (and_congr (not_congr (normalization_5378 r0_node r2_node)) (normalization_5410 r0_node r2_node)))

theorem normalization_5412 (r0_depth r2_depth : Int) : (r2_depth = ((-1 : Int) + r0_depth)) ↔ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_5413 (r0_depth r2_depth : Int) : (¬ (r2_depth = ((-1 : Int) + r0_depth))) ↔ (¬ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) := (not_congr (normalization_5412 r0_depth r2_depth))

theorem normalization_5414 (r0_node r2_node : Int) : (r2_node ≤ (r0_node / (2 : Int))) ↔ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5415 (r0_node r2_node : Int) : (¬ (r2_node ≤ (r0_node / (2 : Int)))) ↔ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) := (not_congr (normalization_5414 r0_node r2_node))

abbrev shared_expr_Repair056_62 (r0_node r2_node : Int) : Prop := ((¬ ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair056_63 (r0_node r2_node r2_sign : Int) : Prop := ((((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair056_62 r0_node r2_node))
theorem normalization_5416 (r0_node r2_node r2_sign : Int) : (((r2_node = (r0_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r0_node / (2 : Int)))) ∧ (¬ (r2_node ≤ (r0_node / (2 : Int)))))) ↔ (shared_expr_Repair056_63 r0_node r2_node r2_sign) := (or_congr (and_congr (normalization_5382 r0_node r2_node) (normalization_183 r2_sign)) (and_congr (not_congr (normalization_5382 r0_node r2_node)) (normalization_5415 r0_node r2_node)))

theorem normalization_5417 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : ((¬ (r2_depth = ((-1 : Int) + r0_depth))) ∨ (((r2_node = (r0_node / (2 : Int))) ∧ (r2_sign = (0 : Int))) ∨ ((¬ (r2_node = (r0_node / (2 : Int)))) ∧ (¬ (r2_node ≤ (r0_node / (2 : Int))))))) ↔ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair056_63 r0_node r2_node r2_sign)) := (or_congr (normalization_5413 r0_depth r2_depth) (normalization_5416 r0_node r2_node r2_sign))

abbrev shared_expr_Repair056_64 (r0_depth r0_node r2_depth r2_node r2_sign : Int) : Prop := ((¬ (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair056_63 r0_node r2_node r2_sign)))
abbrev shared_expr_Repair056_65 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair056_48 r0_node r0_sign r2_node)) ∨ (shared_expr_Repair056_64 r0_depth r0_node r2_depth r2_node r2_sign))
theorem normalization_5418 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : (formula_1559 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair056_65 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_5408 r0_depth r2_depth) (normalization_5411 r0_node r0_sign r2_node)) (and_congr (not_congr (normalization_5408 r0_depth r2_depth)) (normalization_5417 r0_depth r0_node r2_depth r2_node r2_sign)))

abbrev shared_expr_Repair056_66 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : Prop := (((((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair056_61 r0_node r0_sign r2_node r2_sign)) ∨ ((¬ (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair056_65 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))
theorem normalization_5419 (r0_depth r0_node r0_sign r2_depth r2_node r2_sign : Int) : (formula_1560 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) ↔ (shared_expr_Repair056_66 r0_depth r0_node r0_sign r2_depth r2_node r2_sign) := (or_congr (and_congr (normalization_5372 r0_depth r2_depth) (normalization_5407 r0_node r0_sign r2_node r2_sign)) (and_congr (not_congr (normalization_5372 r0_depth r2_depth)) (normalization_5418 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))

theorem normalization_5420 (r0_depth r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : ((r2_kind = (2 : Int)) ∨ (formula_1560 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)) ↔ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair056_66 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)) := (or_congr (normalization_201 r2_kind) (normalization_5419 r0_depth r0_node r0_sign r2_depth r2_node r2_sign))

abbrev shared_expr_Repair056_67 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∧ (¬ (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int))))) ∧ ((((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) ∨ (shared_expr_Repair056_66 r0_depth r0_node r0_sign r2_depth r2_node r2_sign)))
theorem normalization_5421 (r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (r2_kind = (0 : Int))) ∧ (¬ (r0_kind = (2 : Int))) ∧ ((r2_kind = (2 : Int)) ∨ (formula_1560 r0_depth r0_node r0_sign r2_depth r2_node r2_sign))) ↔ (shared_expr_Repair056_67 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign) := (and_congr (normalization_2498 r2_kind) (and_congr (normalization_2320 r0_kind) (normalization_5420 r0_depth r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair056_68 (r0_group r0_kind r0_level r0_mode r2_group r2_kind r2_level r2_mode : Int) : Prop := ((((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair056_60 r0_group r0_level r0_mode r2_group r2_level r2_mode)))
abbrev shared_expr_Repair056_69 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair056_68 r0_group r0_kind r0_level r0_mode r2_group r2_kind r2_level r2_mode) ∨ ((¬ (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair056_67 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))
theorem normalization_5422 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1561 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair056_69 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (or_congr (and_congr (normalization_1438 r0_kind) (normalization_5404 r0_group r0_level r0_mode r2_group r2_kind r2_level r2_mode)) (and_congr (not_congr (normalization_1438 r0_kind)) (normalization_5421 r0_depth r0_kind r0_node r0_sign r2_depth r2_kind r2_node r2_sign)))

abbrev shared_expr_Repair056_70 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : Prop := ((shared_expr_Repair056_57 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair056_69 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))
theorem normalization_5423 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1562 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ (shared_expr_Repair056_70 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := (iff_congr (normalization_5391 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (normalization_5422 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign))

-- Checked replay of rewrite.
theorem replay_3292 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) : (formula_1562 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  classical
  have ht := (normalized_1360 (((r0_kind) ≤ (0 : Int)) ∧ (¬ ((r0_kind) ≤ (-1 : Int)))) (((r2_kind) ≤ (0 : Int)) ∧ (¬ ((r2_kind) ≤ (-1 : Int)))) ((r0_mode) ≤ (3 : Int)) ((r2_mode) ≤ (3 : Int)) (((r0_level + ((-1 : Int) * r2_level)) ≤ (0 : Int)) ∧ (¬ ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)))) ((r0_level + ((-1 : Int) * r2_level)) ≤ (-1 : Int)) (((r0_mode + ((-1 : Int) * r2_mode)) ≤ (0 : Int)) ∧ (¬ ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)))) ((r0_mode + ((-1 : Int) * r2_mode)) ≤ (-1 : Int)) ((r0_group + ((-1 : Int) * r2_group)) ≤ (-1 : Int)) (((r0_kind) ≤ (2 : Int)) ∧ (¬ ((r0_kind) ≤ (1 : Int)))) ((r2_kind) ≤ (1 : Int)) ((r2_kind) ≤ (0 : Int)) (((r2_kind) ≤ (2 : Int)) ∧ (¬ ((r2_kind) ≤ (1 : Int)))) (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (((r0_node + ((-1 : Int) * r2_node)) ≤ (0 : Int)) ∧ (¬ ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))) ((((r0_sign) ≤ (1 : Int)) ∧ (¬ ((r0_sign) ≤ (0 : Int)))) ∧ (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int))))) ((r0_node + ((-1 : Int) * r2_node)) ≤ (-1 : Int)) (((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∧ (¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (-2 : Int)))) (shared_expr_Repair056_48 r0_node r0_sign r2_node) ((¬ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∧ ((r0_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ((¬ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int))) ∧ (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (0 : Int))) (((r2_sign) ≤ (0 : Int)) ∧ (¬ ((r2_sign) ≤ (-1 : Int)))) (((r0_node / (2 : Int)) + ((-1 : Int) * r2_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5423 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) hn

end H4Formal.Generated.Repair
