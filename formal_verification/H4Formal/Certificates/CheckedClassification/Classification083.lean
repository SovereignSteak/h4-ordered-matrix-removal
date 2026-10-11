import H4Formal.Certificates.CheckedClassification.Classification082

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem propositional_1952 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6))))) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ p0) ∧ (¬ p9)))) ∨ p0 ∨ (¬ p9)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5193 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : ((¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))) := by
  exact (propositional_1952 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_5194 (c2_depth c2_kind c2_sign r2_group r2_level : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) : (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5193 c2_depth c2_kind c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i291 l1))) (fun t1 => (False.elim (t1 i231))))))

-- Checked replay of unit-resolution.
theorem replay_5195 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) : ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5192 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5194 c2_depth c2_kind c2_sign r2_group r2_level i291 i231) t0))))

theorem propositional_1953 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5196 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ∨ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (propositional_1953 (r2_mode ≤ (3 : Int)) (r2_mode ≥ (3 : Int)) (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level))

theorem propositional_1954 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))) ∨ ((¬ p0) ∧ (¬ p7)))) ∨ p0 ∨ (¬ p7)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5197 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : ((¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ (formula_1170 c2_depth c2_kind c2_sign r2_level))) := by
  exact (propositional_1954 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((c2_node % (2 : Int)) ≥ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) (formula_1170 c2_depth c2_kind c2_sign r2_level))

-- Checked replay of unit-resolution.
theorem replay_5198 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) : (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5197 c2_depth c2_kind c2_node c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i291 l1))) (fun t1 => (False.elim (t1 i292))))))

-- Checked replay of unit-resolution.
theorem replay_5199 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) : ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5196 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5198 c2_depth c2_kind c2_node c2_sign r2_group r2_level i291 i292) t0))))

-- Checked replay of unit-resolution.
theorem replay_5200 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i291 : (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))))) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : False := by
  exact (Or.elim (replay_5182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (False.elim (l0 i293))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5191 c2_depth c2_kind c2_sign r2_group r2_level r2_mode i291 i231)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_5195 c2_depth c2_kind c2_sign r2_group r2_level r2_mode i291 i231)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_5187 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i291 i292)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_5199 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i291 i292)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i294))) (fun t5 => (False.elim (t5 i295))))))))))))))

abbrev shared_expr_Classification083_0 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) ∨ (¬ (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) ∨ (¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ (formula_1170 c2_depth c2_kind c2_sign r2_level)) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))
abbrev formula_2246 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification083_0 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)

-- Checked replay of lemma.
theorem replay_5201 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_2246 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5200 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

-- Checked replay of unit-resolution.
theorem replay_5202 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) := by
  exact (Or.elim (replay_5201 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i293))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i294))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i295))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i292))) (fun t4 => (False.elim (t4 i231))))))))))))

-- Checked replay of unit-resolution.
theorem replay_5203 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i296 : (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5184 c2_depth c2_kind c2_node c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5202 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i294 i295 i293)))) (fun t1 => (False.elim (t1 i296))))))

-- Checked replay of unit-resolution.
theorem replay_5204 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i296 : (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : ((¬ (r2_mode ≤ (2 : Int))) ∨ (¬ (r2_mode ≥ (2 : Int))) ∨ (¬ (formula_1175 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5183 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5203 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i296 i294 i295 i293) t0))))

theorem propositional_1955 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5205 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : ((¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ (formula_1170 c2_depth c2_kind c2_sign r2_level))) := by
  exact (propositional_1955 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (formula_1170 c2_depth c2_kind c2_sign r2_level) (c2_kind ≤ (2 : Int)) (c2_kind ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5206 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5205 c2_depth c2_kind c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5202 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i294 i295 i293)))) (fun t1 => (False.elim (t1 i292))))))

-- Checked replay of unit-resolution.
theorem replay_5207 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5188 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5206 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i294 i295 i293) t0))))

theorem propositional_1956 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5208 (c2_depth c2_kind c2_sign r2_group r2_level : Int) : ((¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)) ∨ (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) := by
  exact (propositional_1956 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (formula_1172 c2_depth c2_kind c2_sign r2_level) (c2_kind ≤ (2 : Int)) (c2_kind ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5209 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i297 : (formula_1172 c2_depth c2_kind c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5208 c2_depth c2_kind c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5202 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i294 i295 i293)))) (fun t1 => (False.elim (t1 i297))))))

-- Checked replay of unit-resolution.
theorem replay_5210 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i297 : (formula_1172 c2_depth c2_kind c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5192 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5209 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i297 i294 i295 i293) t0))))

theorem propositional_1957 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5211 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) : ((¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) ∨ (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (¬ (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level))) := by
  exact (propositional_1957 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5212 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i298 : (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5211 c2_depth c2_kind c2_node c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5202 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i294 i295 i293)))) (fun t1 => (False.elim (t1 i298))))))

-- Checked replay of unit-resolution.
theorem replay_5213 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i298 : (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5196 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5212 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i298 i294 i295 i293) t0))))

-- Checked replay of unit-resolution.
theorem replay_5214 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i297 : (formula_1172 c2_depth c2_kind c2_sign r2_level)) (i296 : (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level)) (i298 : (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : False := by
  exact (Or.elim (replay_5182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (False.elim (l0 i293))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5207 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i294 i295 i293)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_5210 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i297 i294 i295 i293)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_5204 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i296 i294 i295 i293)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_5213 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode i231 i292 i298 i294 i295 i293)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i294))) (fun t5 => (False.elim (t5 i295))))))))))))))

abbrev shared_expr_Classification083_1 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ (formula_1170 c2_depth c2_kind c2_sign r2_level)) ∨ (¬ (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) ∨ (¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ (¬ (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level)) ∨ (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level)) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))
abbrev formula_2247 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification083_1 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)

-- Checked replay of lemma.
theorem replay_5215 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_2247 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5214 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))) (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

theorem propositional_1958 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5216 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : ((formula_1176 c2_depth c2_kind c2_node c2_sign r2_level) ∨ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  exact (propositional_1958 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((c2_node % (2 : Int)) ≥ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5217 (c2_depth c2_kind c2_node c2_sign r2_level : Int) (i299 : (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))))) : (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level) := by
  exact (Or.elim (replay_5216 c2_depth c2_kind c2_node c2_sign r2_level) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (i299 t0))))

theorem propositional_1959 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5218 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : ((formula_1174 c2_depth c2_kind c2_node c2_sign r2_level) ∨ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  exact (propositional_1959 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((c2_node % (2 : Int)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5219 (c2_depth c2_kind c2_node c2_sign r2_level : Int) (i299 : (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))))) : (formula_1174 c2_depth c2_kind c2_node c2_sign r2_level) := by
  exact (Or.elim (replay_5218 c2_depth c2_kind c2_node c2_sign r2_level) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (i299 t0))))

-- Checked replay of unit-resolution.
theorem replay_5220 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i231 : ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) (i299 : (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))))) (i292 : (formula_1170 c2_depth c2_kind c2_sign r2_level)) (i297 : (formula_1172 c2_depth c2_kind c2_sign r2_level)) (i294 : ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i295 : ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) (i293 : (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) : False := by
  exact (Or.elim (replay_5215 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (False.elim (l0 i292))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i293))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i294))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i295))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_5217 c2_depth c2_kind c2_node c2_sign r2_level i299)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_5219 c2_depth c2_kind c2_node c2_sign r2_level i299)))) (fun t5 => (Or.elim t5 (fun l6 => (False.elim (l6 i297))) (fun t6 => (False.elim (t6 i231))))))))))))))))

abbrev shared_expr_Classification083_2 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ∨ (¬ (formula_1182 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)) ∨ (¬ ((¬ (r2_mode ≤ (5 : Int))) ∨ (¬ (r2_mode ≥ (5 : Int))) ∨ (¬ (formula_1181 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level)) ∨ (¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level)))) ∨ (¬ (formula_1170 c2_depth c2_kind c2_sign r2_level)) ∨ (¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))))
abbrev formula_2248 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification083_2 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode)

-- Checked replay of lemma.
theorem replay_5221 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (formula_2248 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5220 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

abbrev shared_expr_Classification083_3 (c1_depth c1_kind c1_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1081 c1_depth c1_kind c1_sign r2_group r2_level)))) ∨ (¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1081 c1_depth c1_kind c1_sign r2_group r2_level)))
abbrev formula_2249 (c1_depth c1_kind c1_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification083_3 c1_depth c1_kind c1_sign r2_group r2_level r2_mode)

theorem propositional_1960 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5222 (c1_depth c1_kind c1_sign r2_group r2_level r2_mode : Int) : (formula_2249 c1_depth c1_kind c1_sign r2_group r2_level r2_mode) := by
  exact (propositional_1960 (r2_mode ≤ (1 : Int)) (r2_mode ≥ (1 : Int)) (formula_1081 c1_depth c1_kind c1_sign r2_group r2_level))

theorem propositional_1961 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((¬ p8) ∨ (¬ p9))))) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p12) ∨ (¬ p13))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5223 (c2_depth c2_kind c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (1 : Int))) ∨ (¬ (r2_mode ≥ (1 : Int))) ∨ (¬ (formula_1173 c2_depth c2_kind c2_sign r2_group r2_level))) ∨ (r2_mode ≥ (1 : Int))) := by
  exact (propositional_1961 (r2_mode ≤ (1 : Int)) (r2_mode ≥ (1 : Int)) (r2_group ≤ (1 : Int)) (r2_group ≥ (1 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) (c2_kind ≤ (2 : Int)) (c2_kind ≥ (2 : Int)))

theorem propositional_1962 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5224 (c2_depth c2_kind c2_sign r2_level : Int) : ((formula_1170 c2_depth c2_kind c2_sign r2_level) ∨ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  exact (propositional_1962 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_5225 (c2_sign : Int) : ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1963 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5226 (c2_sign : Int) : (((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ∨ (c2_sign ≤ (1 : Int))) := by
  exact (propositional_1963 (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

abbrev shared_expr_Classification083_4 (c2_sign : Int) : Prop := ((¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))
abbrev formula_2250 (c2_sign : Int) : Prop := (shared_expr_Classification083_4 c2_sign)

theorem propositional_1964 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5227 (c2_sign : Int) : (formula_2250 c2_sign) := by
  exact (propositional_1964 ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))) ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_5228 (c2_sign : Int) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i301 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) : (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) := by
  exact (Or.elim (replay_5227 c2_sign) (fun l0 => (False.elim (l0 i301))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i300))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_5229 (c2_sign : Int) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i301 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) : (c2_sign ≤ (1 : Int)) := by
  exact (Or.elim (replay_5226 c2_sign) (fun l0 => (False.elim ((replay_5228 c2_sign i300 i301) l0))) (fun t0 => t0))

theorem propositional_1965 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5230 (c2_sign : Int) : (((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))) ∨ (c2_sign ≥ (2 : Int))) := by
  exact (propositional_1965 (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)))

abbrev shared_expr_Classification083_5 (c2_sign : Int) : Prop := ((¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))
abbrev formula_2251 (c2_sign : Int) : Prop := (shared_expr_Classification083_5 c2_sign)

theorem propositional_1966 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5231 (c2_sign : Int) : (formula_2251 c2_sign) := by
  exact (propositional_1966 ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))) ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_5232 (c2_sign : Int) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i302 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_5231 c2_sign) (fun l0 => (False.elim (l0 i302))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i300))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_5233 (c2_sign : Int) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i302 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : (c2_sign ≥ (2 : Int)) := by
  exact (Or.elim (replay_5230 c2_sign) (fun l0 => (False.elim ((replay_5232 c2_sign i300 i302) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5234 (c2_sign : Int) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i301 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) (i302 : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : False := by
  exact (Or.elim (replay_5225 c2_sign) (fun l0 => (False.elim (l0 (replay_5229 c2_sign i300 i301)))) (fun t0 => (False.elim (t0 (replay_5233 c2_sign i300 i302)))))

abbrev shared_expr_Classification083_6 (c2_sign : Int) : Prop := ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))))
abbrev formula_2252 (c2_sign : Int) : Prop := (shared_expr_Classification083_6 c2_sign)

-- Checked replay of lemma.
theorem replay_5235 (c2_sign : Int) : (formula_2252 c2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5234 c2_sign (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))))

abbrev shared_expr_Classification083_7 (c2_depth c2_sign h : Int) : Prop := ((¬ (formula_581 c2_depth c2_sign h)) ∨ (¬ ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))))) ∨ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))))
abbrev formula_2253 (c2_depth c2_sign h : Int) : Prop := (shared_expr_Classification083_7 c2_depth c2_sign h)

theorem propositional_1967 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5236 (c2_depth c2_sign h : Int) : (formula_2253 c2_depth c2_sign h) := by
  exact (propositional_1967 ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)))

theorem propositional_1968 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5237 (c2_depth h : Int) : (((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) ∨ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  exact (propositional_1968 ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_5238 (c2_depth h r2_level : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i304 : ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i303 : (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) : False := by
  classical
  have k0 := i303
  have k1 := i304
  have k2 := i305
  first | omega | grind (splits := 40)

-- Checked replay of lemma.
theorem replay_5239 (c2_depth h r2_level : Int) : ((¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int)))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5238 c2_depth h r2_level (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))) (Classical.byContradiction (fun q => nc (Or.inl q))) (fun q => nc (Or.inr (Or.inl q))))

-- Checked replay of th-lemma.
theorem replay_5240 (c2_depth r2_level : Int) : ((¬ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1969 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5241 (c2_depth c2_kind c2_sign r2_level : Int) : ((formula_1172 c2_depth c2_kind c2_sign r2_level) ∨ ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) := by
  exact (propositional_1969 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5242 (c2_depth c2_kind c2_sign r2_level : Int) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) := by
  exact (Or.elim (replay_5241 c2_depth c2_kind c2_sign r2_level) (fun l0 => (False.elim (i306 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5243 (c2_depth c2_kind c2_sign r2_level : Int) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : (¬ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_5240 c2_depth r2_level) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_5242 c2_depth c2_kind c2_sign r2_level i306)))))

-- Checked replay of unit-resolution.
theorem replay_5244 (c2_depth c2_kind c2_sign h r2_level : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  exact (Or.elim (replay_5239 c2_depth h r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_5243 c2_depth c2_kind c2_sign r2_level i306) l1))) (fun t1 => (False.elim (t1 i305))))))

-- Checked replay of unit-resolution.
theorem replay_5245 (c2_depth c2_kind c2_sign h r2_level : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : ((¬ ((h + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) := by
  exact (Or.elim (replay_5237 c2_depth h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_5244 c2_depth c2_kind c2_sign h r2_level i305 i306) t0))))

-- Checked replay of unit-resolution.
theorem replay_5246 (c2_depth c2_kind c2_sign h r2_level : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i307 : (formula_581 c2_depth c2_sign h)) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))))) := by
  exact (Or.elim (replay_5236 c2_depth c2_sign h) (fun l0 => (False.elim (l0 i307))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5245 c2_depth c2_kind c2_sign h r2_level i305 i306)))) (fun t1 => (Or.elim t1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))))

-- Checked replay of unit-resolution.
theorem replay_5247 (c2_depth c2_kind c2_sign h r2_level : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i307 : (formula_581 c2_depth c2_sign h)) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : (¬ ((¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  exact (Or.elim (replay_5235 c2_sign) (fun l0 => (False.elim (l0 i300))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5246 c2_depth c2_kind c2_sign h r2_level i305 i307 i306)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_5248 (c2_depth c2_kind c2_sign h r2_level : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i307 : (formula_581 c2_depth c2_sign h)) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : (formula_1170 c2_depth c2_kind c2_sign r2_level) := by
  exact (Or.elim (replay_5224 c2_depth c2_kind c2_sign r2_level) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim ((replay_5247 c2_depth c2_kind c2_sign h r2_level i305 i300 i307 i306) t0))))

-- Checked replay of unit-resolution.
theorem replay_5249 (c2_depth c2_kind c2_sign h r2_group r2_level : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i308 : ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i307 : (formula_581 c2_depth c2_sign h)) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5205 c2_depth c2_kind c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i308))) (fun t1 => (False.elim (t1 (replay_5248 c2_depth c2_kind c2_sign h r2_level i305 i300 i307 i306)))))))

-- Checked replay of unit-resolution.
theorem replay_5250 (c2_depth c2_kind c2_sign h r2_group r2_level r2_mode : Int) (i305 : ((h + ((-1 : Int) * r2_level)) ≥ (0 : Int))) (i308 : ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) (i300 : ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))) (i307 : (formula_581 c2_depth c2_sign h)) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : ((¬ (r2_mode ≤ (0 : Int))) ∨ (¬ (r2_mode ≥ (0 : Int))) ∨ (¬ (formula_1171 c2_depth c2_kind c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5188 c2_depth c2_kind c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5249 c2_depth c2_kind c2_sign h r2_group r2_level i305 i308 i300 i307 i306) t0))))

theorem propositional_1970 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p8) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5251 (c2_depth c2_kind c2_node c2_sign r2_level : Int) : ((formula_1176 c2_depth c2_kind c2_node c2_sign r2_level) ∨ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) := by
  exact (propositional_1970 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((c2_node % (2 : Int)) ≥ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5252 (c2_depth c2_kind c2_node c2_sign r2_level : Int) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : (formula_1176 c2_depth c2_kind c2_node c2_sign r2_level) := by
  exact (Or.elim (replay_5251 c2_depth c2_kind c2_node c2_sign r2_level) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim ((replay_5243 c2_depth c2_kind c2_sign r2_level i306) t0))))

-- Checked replay of unit-resolution.
theorem replay_5253 (c2_depth c2_kind c2_node c2_sign r2_group r2_level : Int) (i308 : ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level)) := by
  exact (Or.elim (replay_5211 c2_depth c2_kind c2_node c2_sign r2_group r2_level) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i308))) (fun t1 => (False.elim (t1 (replay_5252 c2_depth c2_kind c2_node c2_sign r2_level i306)))))))

-- Checked replay of unit-resolution.
theorem replay_5254 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) (i308 : ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) (i306 : (¬ (formula_1172 c2_depth c2_kind c2_sign r2_level))) : ((¬ (r2_mode ≤ (3 : Int))) ∨ (¬ (r2_mode ≥ (3 : Int))) ∨ (¬ (formula_1177 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) := by
  exact (Or.elim (replay_5196 c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5253 c2_depth c2_kind c2_node c2_sign r2_group r2_level i308 i306) t0))))

theorem propositional_1971 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5255 (c2_depth c2_kind c2_node c2_sign r2_group r2_level r2_mode : Int) : (((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1179 c2_depth c2_kind c2_node c2_sign r2_group r2_level))) ∨ (r2_mode ≥ (4 : Int))) := by
  exact (propositional_1971 (r2_mode ≤ (4 : Int)) (r2_mode ≥ (4 : Int)) (r2_group ≤ (1 : Int)) (r2_group ≥ (1 : Int)) (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((c2_node % (2 : Int)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))

abbrev shared_expr_Classification083_8 (c1_depth c1_kind c1_node c1_sign r2_group r2_level r2_mode : Int) : Prop := ((¬ ((¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1087 c1_depth c1_kind c1_node c1_sign r2_group r2_level)))) ∨ (¬ (r2_mode ≤ (4 : Int))) ∨ (¬ (r2_mode ≥ (4 : Int))) ∨ (¬ (formula_1087 c1_depth c1_kind c1_node c1_sign r2_group r2_level)))
abbrev formula_2254 (c1_depth c1_kind c1_node c1_sign r2_group r2_level r2_mode : Int) : Prop := (shared_expr_Classification083_8 c1_depth c1_kind c1_node c1_sign r2_group r2_level r2_mode)

theorem propositional_1972 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5256 (c1_depth c1_kind c1_node c1_sign r2_group r2_level r2_mode : Int) : (formula_2254 c1_depth c1_kind c1_node c1_sign r2_group r2_level r2_mode) := by
  exact (propositional_1972 (r2_mode ≤ (4 : Int)) (r2_mode ≥ (4 : Int)) (formula_1087 c1_depth c1_kind c1_node c1_sign r2_group r2_level))

theorem propositional_1973 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7))))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5257 (c1_depth c1_kind c1_node c1_sign r2_group r2_level : Int) : ((formula_1087 c1_depth c1_kind c1_node c1_sign r2_group r2_level) ∨ (¬ ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int))))) ∨ (formula_1080 c1_depth c1_kind c1_sign r2_level)) := by
  exact (propositional_1973 ((¬ (r2_group ≤ (1 : Int))) ∨ (¬ (r2_group ≥ (1 : Int)))) (formula_1080 c1_depth c1_kind c1_sign r2_level) (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)) ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))) ((c1_node % (2 : Int)) ≤ (0 : Int)) ((r2_level + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ((r2_level + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))

abbrev shared_expr_Classification083_9 (c1_depth c1_kind c1_sign r2_level : Int) : Prop := ((¬ (formula_1080 c1_depth c1_kind c1_sign r2_level)) ∨ (¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))))
abbrev formula_2255 (c1_depth c1_kind c1_sign r2_level : Int) : Prop := (shared_expr_Classification083_9 c1_depth c1_kind c1_sign r2_level)

theorem propositional_1974 (p0 p1 p2 p3 p4 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5258 (c1_depth c1_kind c1_sign r2_level : Int) : (formula_2255 c1_depth c1_kind c1_sign r2_level) := by
  exact (propositional_1974 (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)) ((¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (2 : Int))) ∨ (¬ (c1_sign ≥ (2 : Int)))))) ((r2_level + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ((r2_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_5259 (c1_depth c2_depth r2_level : Int) : ((¬ ((c1_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r2_level + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∨ ((r2_level + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1975 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5260 (c2_sign : Int) : (((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int)))) ∨ (c2_sign ≤ (0 : Int))) := by
  exact (propositional_1975 (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)))

abbrev shared_expr_Classification083_10 (c2_sign : Int) : Prop := ((¬ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))
abbrev formula_2256 (c2_sign : Int) : Prop := (shared_expr_Classification083_10 c2_sign)

theorem propositional_1976 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5261 (c2_sign : Int) : (formula_2256 c2_sign) := by
  exact (propositional_1976 ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))

theorem propositional_1977 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5262 (c2_sign : Int) : (((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) ∨ (c2_sign ≥ (1 : Int))) := by
  exact (propositional_1977 (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5263 (c2_sign : Int) (i257 : (¬ (c2_sign ≥ (1 : Int)))) : ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int)))) := by
  exact (Or.elim (replay_5262 c2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i257 t0))))

-- Checked replay of unit-resolution.
theorem replay_5264 (c2_sign : Int) (i257 : (¬ (c2_sign ≥ (1 : Int)))) (i309 : ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_5261 c2_sign) (fun l0 => (False.elim (l0 i309))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5263 c2_sign i257)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_5265 (c2_sign : Int) (i257 : (¬ (c2_sign ≥ (1 : Int)))) : (¬ (c2_sign ≥ (2 : Int))) := by
  exact (Or.elim (replay_3714 c2_sign) (fun l0 => (False.elim (i257 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5266 (c2_sign : Int) (i257 : (¬ (c2_sign ≥ (1 : Int)))) (i309 : ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) : False := by
  exact (Or.elim (replay_5230 c2_sign) (fun l0 => (False.elim ((replay_5264 c2_sign i257 i309) l0))) (fun t0 => (False.elim ((replay_5265 c2_sign i257) t0))))

-- Checked replay of lemma.
theorem replay_5267 (c2_sign : Int) : ((c2_sign ≥ (1 : Int)) ∨ (¬ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5266 c2_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

theorem propositional_1978 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p4) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5268 (c2_depth c2_kind c2_sign r0_level : Int) : ((formula_245 c2_depth c2_kind c2_sign r0_level) ∨ ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int))))))) := by
  exact (propositional_1978 (c2_kind ≤ (1 : Int)) (c2_kind ≥ (1 : Int)) ((r0_level + ((-1 : Int) * c2_depth)) ≤ (1 : Int)) ((r0_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ((¬ ((¬ (c2_sign ≤ (1 : Int))) ∨ (¬ (c2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_sign ≤ (2 : Int))) ∨ (¬ (c2_sign ≥ (2 : Int)))))))

theorem propositional_1979 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5269 (r0_kind : Int) : ((¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) ∨ (¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) := by
  exact (propositional_1979 (r0_kind ≤ (0 : Int)) (r0_kind ≥ (0 : Int)))

theorem propositional_1980 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p15)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5270 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_1041 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (r0_kind ≥ (0 : Int))) := by
  exact (propositional_1980 (r0_mode ≥ (6 : Int)) (r0_depth ≥ (0 : Int)) (r0_group ≤ (1 : Int)) (r0_group ≥ (1 : Int)) (r0_group ≤ (2 : Int)) (r0_group ≥ (2 : Int)) (r0_kind ≤ (0 : Int)) (r0_kind ≥ (0 : Int)) ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int)) (r0_sign ≥ (0 : Int)) (r0_sign ≤ (0 : Int)) (r0_depth ≤ (0 : Int)) (r0_level ≥ (1 : Int)) (r0_mode ≥ (0 : Int)) (r0_node ≥ (0 : Int)) (r0_node ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5271 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i310 : (¬ (formula_1041 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : (r0_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_5270 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (False.elim (i310 l0))) (fun t0 => t0))

theorem propositional_1981 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14) ∨ (¬ p15)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5272 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_1041 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (r0_kind ≤ (0 : Int))) := by
  exact (propositional_1981 (r0_mode ≥ (6 : Int)) (r0_depth ≥ (0 : Int)) (r0_group ≤ (1 : Int)) (r0_group ≥ (1 : Int)) (r0_group ≤ (2 : Int)) (r0_group ≥ (2 : Int)) (r0_kind ≤ (0 : Int)) (r0_kind ≥ (0 : Int)) ((h + ((-1 : Int) * r0_level)) ≥ (0 : Int)) (r0_sign ≥ (0 : Int)) (r0_sign ≤ (0 : Int)) (r0_depth ≤ (0 : Int)) (r0_level ≥ (1 : Int)) (r0_mode ≥ (0 : Int)) (r0_node ≥ (0 : Int)) (r0_node ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5273 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i310 : (¬ (formula_1041 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : (r0_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_5272 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (False.elim (i310 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5274 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i311 : ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int))))) (i310 : (¬ (formula_1041 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : False := by
  exact (Or.elim (replay_5269 r0_kind) (fun l0 => (False.elim (l0 i311))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5273 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i310)))) (fun t1 => (False.elim (t1 (replay_5271 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i310)))))))

-- Checked replay of lemma.
theorem replay_5275 (h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_1041 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (¬ ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_5274 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign (Classical.byContradiction (fun q => nc (Or.inr q))) (fun q => nc (Or.inl q)))

-- Checked replay of th-lemma.
theorem replay_5276 (r0_kind : Int) : ((¬ (r0_kind ≤ (0 : Int))) ∨ (r0_kind ≤ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_5277 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i312 : (¬ (formula_1040 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : (r0_kind ≥ (2 : Int)) := by
  exact (Or.elim (replay_2005 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) (fun l0 => (False.elim (i312 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_5278 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i312 : (¬ (formula_1040 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : (¬ (r0_kind ≤ (1 : Int))) := by
  exact (Or.elim (replay_1730 r0_kind) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_5277 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i312)))))

-- Checked replay of unit-resolution.
theorem replay_5279 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i312 : (¬ (formula_1040 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : (¬ (r0_kind ≤ (0 : Int))) := by
  exact (Or.elim (replay_5276 r0_kind) (fun l0 => l0) (fun t0 => (False.elim ((replay_5278 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i312) t0))))

-- Checked replay of unit-resolution.
theorem replay_5280 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) (i312 : (¬ (formula_1040 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign))) : ((¬ (r0_kind ≤ (0 : Int))) ∨ (¬ (r0_kind ≥ (0 : Int)))) := by
  exact (Or.elim (replay_1460 r0_kind) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_5279 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign i312) t0))))

theorem propositional_1982 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5281 (r0_kind : Int) : ((¬ ((¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int))))) ∨ (¬ (r0_kind ≤ (2 : Int))) ∨ (¬ (r0_kind ≥ (2 : Int)))) := by
  exact (propositional_1982 (r0_kind ≤ (2 : Int)) (r0_kind ≥ (2 : Int)))

theorem propositional_1983 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p10) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5282 (r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign : Int) : ((formula_1040 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ∨ (r0_kind ≤ (2 : Int))) := by
  exact (propositional_1983 (r0_depth ≥ (0 : Int)) (r0_mode ≤ (0 : Int)) (r0_group ≤ (0 : Int)) (r0_group ≥ (0 : Int)) (r0_level ≥ (0 : Int)) (r0_level ≤ (0 : Int)) (r0_sign ≥ (0 : Int)) (r0_sign ≤ (0 : Int)) (r0_kind ≥ (2 : Int)) (r0_depth ≤ (0 : Int)) (r0_kind ≤ (2 : Int)) (r0_mode ≥ (0 : Int)) (r0_node ≥ (0 : Int)) (r0_node ≤ (0 : Int)))

end H4Formal.Generated.Classification
