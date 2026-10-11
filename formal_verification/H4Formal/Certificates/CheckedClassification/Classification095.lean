import H4Formal.Certificates.CheckedClassification.Classification094

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of unit-resolution.
theorem replay_6160 (c2_depth c3_depth r1_depth r2_depth r3_depth : Int) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i370 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) (i404 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (i405 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) : (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_6159 c2_depth c3_depth r1_depth r2_depth r3_depth) (fun l0 => (False.elim (l0 i361))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i370))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (i404 l2))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i405))) (fun t3 => t3))))))))

-- Checked replay of unit-resolution.
theorem replay_6161 (c2_depth c3_depth c3_node c3_sign h r1_depth r2_depth r3_depth r3_node r3_sign : Int) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i370 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) (i404 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (i405 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) : ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2512 c3_node c3_sign h r3_depth r3_node r3_sign))) := by
  exact (Or.elim (replay_6158 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6160 c2_depth c3_depth r1_depth r2_depth r3_depth i361 i370 i404 i405) t0))))

-- Checked replay of unit-resolution.
theorem replay_6162 (c2_depth c3_depth c3_kind c3_node c3_sign h r1_depth r2_depth r3_depth r3_kind r3_node r3_sign : Int) (i148 : ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))))) (i382 : ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i370 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) (i404 : (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)))) (i405 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) (i397 : (formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) : False := by
  exact (Or.elim (replay_5962 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim (l0 i397))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i148))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i382))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6161 c2_depth c3_depth c3_node c3_sign h r1_depth r2_depth r3_depth r3_node r3_sign i361 i370 i404 i405)))) (fun t3 => (False.elim (t3 (replay_6157 c2_depth c3_depth c3_node c3_sign r1_depth r2_depth r3_depth r3_node r3_sign i361 i370 i404 i405)))))))))))

abbrev shared_expr_Classification095_0 (c2_depth c3_depth c3_kind c3_node c3_sign h r1_depth r2_depth r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) ∨ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int)) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))))
abbrev formula_2537 (c2_depth c3_depth c3_kind c3_node c3_sign h r1_depth r2_depth r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification095_0 c2_depth c3_depth c3_kind c3_node c3_sign h r1_depth r2_depth r3_depth r3_kind r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_6163 (c2_depth c3_depth c3_kind c3_node c3_sign h r1_depth r2_depth r3_depth r3_kind r3_node r3_sign : Int) : (formula_2537 c2_depth c3_depth c3_kind c3_node c3_sign h r1_depth r2_depth r3_depth r3_kind r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6162 c2_depth c3_depth c3_kind c3_node c3_sign h r1_depth r2_depth r3_depth r3_kind r3_node r3_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))) (Classical.byContradiction (fun q => nc (Or.inl q))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))))

abbrev shared_expr_Classification095_1 (r2_node r3_node : Int) : Prop := (((¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))) ∨ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))
abbrev formula_2538 (r2_node r3_node : Int) : Prop := (shared_expr_Classification095_1 r2_node r3_node)

theorem propositional_2211 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6164 (r2_node r3_node : Int) : (formula_2538 r2_node r3_node) := by
  exact (propositional_2211 ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Classification095_2 (r2_node r2_sign r3_node : Int) : Prop := ((¬ (formula_77 r2_node r2_sign r3_node)) ∨ (¬ ((¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))))) ∨ (¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2539 (r2_node r2_sign r3_node : Int) : Prop := (shared_expr_Classification095_2 r2_node r2_sign r3_node)

theorem propositional_2212 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6165 (r2_node r2_sign r3_node : Int) : (formula_2539 r2_node r2_sign r3_node) := by
  exact (propositional_2212 ((¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))) ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_6166 (c1_node r2_node r3_node : Int) (i408 : (¬ ((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))) (i406 : ((r2_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) (i407 : (¬ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))) : False := by
  classical
  have k0 := i406
  have k1 := i407
  have k2 := i408
  first | omega | grind (splits := 40)

-- Checked replay of lemma.
theorem replay_6167 (c1_node r2_node r3_node : Int) : (((r2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)) ∨ (¬ ((r2_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ∨ ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6166 c1_node r2_node r3_node (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inr (Or.inr q))))

abbrev shared_expr_Classification095_3 (c1_node c1_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ (formula_1070 c1_node c1_sign h r2_depth r2_node r2_sign)) ∨ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∨ ((r2_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) ∨ (¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))
abbrev formula_2540 (c1_node c1_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification095_3 c1_node c1_sign h r2_depth r2_node r2_sign)

theorem propositional_2213 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ (p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6168 (c1_node c1_sign h r2_depth r2_node r2_sign : Int) : (formula_2540 c1_node c1_sign h r2_depth r2_node r2_sign) := by
  exact (propositional_2213 ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)))

theorem propositional_2214 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ (¬ ((¬ p1) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10))) ∨ (¬ p11)) ∨ p11) := by
  classical
  first | (by_cases case_p11 : p11 <;> simp [case_p11, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6169 (c1_node c1_sign h r2_depth r2_node r2_sign : Int) : ((formula_1071 c1_node c1_sign h r2_depth r2_node r2_sign) ∨ (formula_1070 c1_node c1_sign h r2_depth r2_node r2_sign)) := by
  exact (propositional_2214 ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((r2_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c1_sign ≤ (2 : Int)) (c1_sign ≥ (2 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)) (formula_1070 c1_node c1_sign h r2_depth r2_node r2_sign))

abbrev shared_expr_Classification095_4 (c1_depth c1_node c1_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1071 c1_node c1_sign h r2_depth r2_node r2_sign)))) ∨ (¬ ((r2_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1071 c1_node c1_sign h r2_depth r2_node r2_sign)))
abbrev formula_2541 (c1_depth c1_node c1_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification095_4 c1_depth c1_node c1_sign h r2_depth r2_node r2_sign)

theorem propositional_2215 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6170 (c1_depth c1_node c1_sign h r2_depth r2_node r2_sign : Int) : (formula_2541 c1_depth c1_node c1_sign h r2_depth r2_node r2_sign) := by
  exact (propositional_2215 ((r2_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) (formula_1071 c1_node c1_sign h r2_depth r2_node r2_sign))

abbrev shared_expr_Classification095_5 (c1_depth c2_depth r2_depth r3_depth : Int) : Prop := (((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) ∨ ((r2_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))
abbrev formula_2542 (c1_depth c2_depth r2_depth r3_depth : Int) : Prop := (shared_expr_Classification095_5 c1_depth c2_depth r2_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_6171 (c1_depth c2_depth r2_depth r3_depth : Int) : (formula_2542 c1_depth c2_depth r2_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification095_6 (c1_node c1_sign r1_node r1_sign : Int) : Prop := ((¬ (formula_2300 c1_node c1_sign r1_node r1_sign)) ∨ ((c1_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))))
abbrev formula_2543 (c1_node c1_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification095_6 c1_node c1_sign r1_node r1_sign)

theorem propositional_2216 (p0 p1 p2 p3 : Prop) : ((¬ (p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3))) ∨ p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> by_cases case_p2 : p2 <;> simp [case_p0, case_p1, case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6172 (c1_node c1_sign r1_node r1_sign : Int) : (formula_2543 c1_node c1_sign r1_node r1_sign) := by
  exact (propositional_2216 ((c1_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))

theorem propositional_2217 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ p4))) ∨ (¬ p5))) ∨ (¬ p6)) ∨ p6) := by
  classical
  first | (by_cases case_p6 : p6 <;> simp [case_p6, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6173 (c1_node c1_sign r1_node r1_sign : Int) : (((¬ (formula_2298 c1_node c1_sign r1_node r1_sign)) ∨ (¬ (formula_2300 c1_node c1_sign r1_node r1_sign))) ∨ (formula_2300 c1_node c1_sign r1_node r1_sign)) := by
  exact (propositional_2217 (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ((c1_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)) (formula_2300 c1_node c1_sign r1_node r1_sign))

-- Checked replay of unit-resolution.
theorem replay_6174 (c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i374 : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) (i371 : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) (i376 : (formula_2301 c1_depth c1_node c1_sign r1_depth r1_node r1_sign)) (i373 : ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) (i370 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) (i372 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) (i359 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) : (¬ ((¬ (formula_2298 c1_node c1_sign r1_node r1_sign)) ∨ (¬ (formula_2300 c1_node c1_sign r1_node r1_sign)))) := by
  exact (Or.elim (replay_5706 c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign) (fun l0 => (False.elim (i369 l0))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i376))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i370))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i371))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i372))) (fun t5 => (Or.elim t5 (fun l6 => (False.elim (l6 i373))) (fun t6 => (Or.elim t6 (fun l7 => (False.elim (i374 l7))) (fun t7 => (False.elim (t7 i359))))))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_6175 (c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i374 : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) (i371 : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) (i376 : (formula_2301 c1_depth c1_node c1_sign r1_depth r1_node r1_sign)) (i373 : ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) (i370 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) (i372 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) (i359 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) : (formula_2300 c1_node c1_sign r1_node r1_sign) := by
  exact (Or.elim (replay_6173 c1_node c1_sign r1_node r1_sign) (fun l0 => (False.elim ((replay_6174 c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign i374 i371 i376 i373 i370 i369 i372 i359) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))))

theorem propositional_2218 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p4) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6176 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ (c1_sign ≤ (1 : Int))) := by
  exact (propositional_2218 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6177 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) (i410 : (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) (i409 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) : (¬ (formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
  exact (Or.elim (replay_5645 c1_node c1_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim (l0 (replay_5691 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i369)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i410))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i409))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_6178 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) (i410 : (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) (i409 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) : (c1_sign ≤ (1 : Int)) := by
  exact (Or.elim (replay_6176 c1_node c1_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_6177 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i410 i409 i369) l0))) (fun t0 => t0))

theorem propositional_2219 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p5) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6179 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ (c1_sign ≥ (1 : Int))) := by
  exact (propositional_2219 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6180 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) (i410 : (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) (i409 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) : (c1_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_6179 c1_node c1_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_6177 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i410 i409 i369) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6181 (c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i374 : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) (i371 : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) (i225 : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i376 : (formula_2301 c1_depth c1_node c1_sign r1_depth r1_node r1_sign)) (i373 : ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) (i370 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) (i410 : (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) (i409 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) (i372 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) (i359 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) : ((c1_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) := by
  exact (Or.elim (replay_6172 c1_node c1_sign r1_node r1_sign) (fun l0 => (False.elim (l0 (replay_6175 c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign i374 i371 i376 i373 i370 i369 i372 i359)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6178 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i410 i409 i369)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6180 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i410 i409 i369)))) (fun t3 => (False.elim (t3 i225))))))))))

theorem propositional_2220 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6182 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : ((formula_1290 c1_node c1_sign h r3_depth r3_node r3_sign) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) := by
  exact (propositional_2220 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6183 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) (i410 : (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) (i409 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) : (¬ ((r3_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_6182 c1_node c1_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_6177 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i410 i409 i369) l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_6184 (c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) (i411 : (¬ ((r3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))) (i374 : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) (i371 : ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) (i225 : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i376 : (formula_2301 c1_depth c1_node c1_sign r1_depth r1_node r1_sign)) (i373 : ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) (i370 : ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) (i410 : (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) (i409 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) (i369 : (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))))) (i372 : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) (i359 : ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))) : False := by
  classical
  have k0 := (replay_6181 c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign i374 i371 i225 i376 i373 i370 i410 i409 i369 i372 i359)
  have k1 := (replay_6183 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i410 i409 i369)
  have k2 := i411
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification095_7 (c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1291 c1_node c1_sign h r3_depth r3_node r3_sign))) ∨ ((r3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ∨ (¬ (formula_1289 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_2301 c1_depth c1_node c1_sign r1_depth r1_node r1_sign)) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (1 : Int))))
abbrev formula_2544 (c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification095_7 c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_6185 (c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign : Int) : (formula_2544 c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6184 c1_depth c1_node c1_sign c2_depth c3_depth h r1_depth r1_node r1_sign r3_depth r3_node r3_sign (fun q => nc (Or.inr (Or.inl q))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))))))))

abbrev shared_expr_Classification095_8 (r1_node r3_node r3_sign : Int) : Prop := ((¬ (formula_2311 r1_node r3_node r3_sign)) ∨ ((¬ ((r3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))))
abbrev formula_2545 (r1_node r3_node r3_sign : Int) : Prop := (shared_expr_Classification095_8 r1_node r3_node r3_sign)

theorem propositional_2221 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ p2)))) ∨ p0 ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6186 (r1_node r3_node r3_sign : Int) : (formula_2545 r1_node r3_node r3_sign) := by
  exact (propositional_2221 ((¬ ((r3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ((r3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))))

-- Checked replay of th-lemma.
theorem replay_6187 (c2_node r1_node r2_node : Int) : (((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ∨ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification095_9 (r1_node r2_node r2_sign : Int) : Prop := ((¬ (formula_20 r1_node r2_node r2_sign)) ∨ ((¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ∨ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))))
abbrev formula_2546 (r1_node r2_node r2_sign : Int) : Prop := (shared_expr_Classification095_9 r1_node r2_node r2_sign)

theorem propositional_2222 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ p2)))) ∨ p0 ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6188 (r1_node r2_node r2_sign : Int) : (formula_2546 r1_node r2_node r2_sign) := by
  exact (propositional_2222 ((¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int)))))

-- Checked replay of unit-resolution.
theorem replay_6189 (r1_depth r1_node r2_depth r2_node r2_sign : Int) (i412 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i362 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) (i366 : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_20 r1_node r2_node r2_sign))) : ((¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))) := by
  exact (Or.elim (replay_6188 r1_node r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_5663 r1_depth r1_node r2_depth r2_node r2_sign i361 i362 i366)))) (fun t0 => (Or.elim t0 (fun l1 => (Or.elim l1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t1 => (False.elim (t1 i412))))))

-- Checked replay of unit-resolution.
theorem replay_6190 (r1_depth r1_node r2_depth r2_node r2_sign : Int) (i412 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i362 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) (i366 : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_20 r1_node r2_node r2_sign))) : (¬ ((r2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) := by
  exact (Or.elim (replay_5654 r1_node r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_5663 r1_depth r1_node r2_depth r2_node r2_sign i361 i362 i366)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6189 r1_depth r1_node r2_depth r2_node r2_sign i412 i361 i362 i366)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6191 (c2_node r1_depth r1_node r2_depth r2_node r2_sign : Int) (i365 : (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) (i412 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i362 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) (i366 : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_20 r1_node r2_node r2_sign))) : (¬ ((c2_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int))) := by
  exact (Or.elim (replay_6187 c2_node r1_node r2_node) (fun l0 => (False.elim (i365 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_6190 r1_depth r1_node r2_depth r2_node r2_sign i412 i361 i362 i366) l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6192 (c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i365 : (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) (i412 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i224 : (c2_sign ≥ (1 : Int))) (i273 : (c2_sign ≤ (1 : Int))) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i362 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) (i366 : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_20 r1_node r2_node r2_sign))) (i225 : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) : (¬ (formula_1824 c2_node c2_sign r1_node r1_sign)) := by
  exact (Or.elim (replay_3606 c2_node c2_sign r1_node r1_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_6191 c2_node r1_depth r1_node r2_depth r2_node r2_sign i365 i412 i361 i362 i366) l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i273))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i224))) (fun t3 => (False.elim (t3 i225))))))))))

-- Checked replay of unit-resolution.
theorem replay_6193 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) (i365 : (¬ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)))) (i412 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i224 : (c2_sign ≥ (1 : Int))) (i273 : (c2_sign ≤ (1 : Int))) (i361 : ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) (i362 : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) (i366 : ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_20 r1_node r2_node r2_sign))) (i225 : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i364 : ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) (i220 : (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) (i363 : ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) : False := by
  exact (Or.elim (replay_3605 c2_node c2_sign r1_node r1_sign) (fun l0 => (False.elim ((replay_5658 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth i362 i364 i220 i363) l0))) (fun t0 => (False.elim ((replay_6192 c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign i365 i412 i224 i273 i361 i362 i366 i225) t0))))

abbrev shared_expr_Classification095_10 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_depth)) ≥ (1 : Int))) ∨ (¬ (formula_1825 c2_depth c2_node c2_sign r1_depth r1_node r1_sign)) ∨ (¬ (c2_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ (c2_sign ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ ((r2_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) ∨ (¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (¬ ((¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≥ (1 : Int))) ∨ (formula_20 r1_node r2_node r2_sign))))
abbrev formula_2547 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Classification095_10 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign)

-- Checked replay of lemma.
theorem replay_6194 (c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign : Int) : (formula_2547 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6193 c2_depth c2_node c2_sign r1_depth r1_node r1_sign r2_depth r2_node r2_sign (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))

theorem propositional_2223 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6195 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) : ((formula_2041 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) ∨ ((¬ (formula_2039 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2040 c3_node c3_sign r1_node r1_sign)))) := by
  exact (propositional_2223 ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((¬ (formula_2039 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2040 c3_node c3_sign r1_node r1_sign))))

abbrev shared_expr_Classification095_11 (c3_node c3_sign r1_node r1_sign : Int) : Prop := ((¬ ((¬ (formula_2039 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2040 c3_node c3_sign r1_node r1_sign)))) ∨ (¬ (formula_2039 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2040 c3_node c3_sign r1_node r1_sign)))
abbrev formula_2548 (c3_node c3_sign r1_node r1_sign : Int) : Prop := (shared_expr_Classification095_11 c3_node c3_sign r1_node r1_sign)

theorem propositional_2224 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6196 (c3_node c3_sign r1_node r1_sign : Int) : (formula_2548 c3_node c3_sign r1_node r1_sign) := by
  exact (propositional_2224 (formula_2039 c3_node c3_sign r1_node r1_sign) (formula_2040 c3_node c3_sign r1_node r1_sign))

theorem propositional_2225 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6197 (c3_node c3_sign r1_node r1_sign : Int) : ((formula_2039 c3_node c3_sign r1_node r1_sign) ∨ (c3_sign ≤ (0 : Int))) := by
  exact (propositional_2225 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6198 (c3_node c3_sign r1_node r1_sign : Int) (i413 : (¬ (c3_sign ≤ (0 : Int)))) : (formula_2039 c3_node c3_sign r1_node r1_sign) := by
  exact (Or.elim (replay_6197 c3_node c3_sign r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim (i413 t0))))

-- Checked replay of unit-resolution.
theorem replay_6199 (c3_node c3_sign r1_node r1_sign : Int) (i413 : (¬ (c3_sign ≤ (0 : Int)))) (i414 : (formula_2040 c3_node c3_sign r1_node r1_sign)) : (¬ ((¬ (formula_2039 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2040 c3_node c3_sign r1_node r1_sign)))) := by
  exact (Or.elim (replay_6196 c3_node c3_sign r1_node r1_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6198 c3_node c3_sign r1_node r1_sign i413)))) (fun t1 => (False.elim (t1 i414))))))

-- Checked replay of unit-resolution.
theorem replay_6200 (c3_depth c3_node c3_sign r1_depth r1_node r1_sign : Int) (i413 : (¬ (c3_sign ≤ (0 : Int)))) (i414 : (formula_2040 c3_node c3_sign r1_node r1_sign)) : (formula_2041 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) := by
  exact (Or.elim (replay_6195 c3_depth c3_node c3_sign r1_depth r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6199 c3_node c3_sign r1_node r1_sign i413 i414) t0))))

abbrev shared_expr_Classification095_12 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign))) ∨ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign))
abbrev formula_2549 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification095_12 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign)

theorem propositional_2226 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6201 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2549 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2226 ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign))

abbrev shared_expr_Classification095_13 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := ((¬ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)))
abbrev formula_2550 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : Prop := (shared_expr_Classification095_13 c3_node c3_sign h r1_depth r1_node r1_sign)

theorem propositional_2227 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6202 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : (formula_2550 c3_node c3_sign h r1_depth r1_node r1_sign) := by
  exact (propositional_2227 (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign) ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign))

theorem propositional_2228 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6203 (c3_node c3_sign r1_node r1_sign : Int) : (((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∨ (c3_sign ≤ (0 : Int))) := by
  exact (propositional_2228 (r1_sign ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6204 (c3_node c3_sign r1_node r1_sign : Int) (i413 : (¬ (c3_sign ≤ (0 : Int)))) : ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) := by
  exact (Or.elim (replay_6203 c3_node c3_sign r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim (i413 t0))))

-- Checked replay of unit-resolution.
theorem replay_6205 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) (i413 : (¬ (c3_sign ≤ (0 : Int)))) (i416 : (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign)) (i415 : (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)) : (¬ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign)) := by
  exact (Or.elim (replay_6202 c3_node c3_sign h r1_depth r1_node r1_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i416))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6204 c3_node c3_sign r1_node r1_sign i413)))) (fun t2 => (False.elim (t2 i415))))))))

-- Checked replay of unit-resolution.
theorem replay_6206 (c3_depth c3_node c3_sign h r1_depth r1_node r1_sign : Int) (i413 : (¬ (c3_sign ≤ (0 : Int)))) (i416 : (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign)) (i415 : (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)) : ((¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2038 c3_node c3_sign h r1_depth r1_node r1_sign))) := by
  exact (Or.elim (replay_6201 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6205 c3_node c3_sign h r1_depth r1_node r1_sign i413 i416 i415) t0))))

-- Checked replay of unit-resolution.
theorem replay_6207 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) (i8 : ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) (i382 : ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) (i413 : (¬ (c3_sign ≤ (0 : Int)))) (i416 : (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign)) (i415 : (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)) (i383 : (formula_2042 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)) (i414 : (formula_2040 c3_node c3_sign r1_node r1_sign)) : False := by
  exact (Or.elim (replay_5790 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim (l0 i383))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i8))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i382))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6206 c3_depth c3_node c3_sign h r1_depth r1_node r1_sign i413 i416 i415)))) (fun t3 => (False.elim (t3 (replay_6200 c3_depth c3_node c3_sign r1_depth r1_node r1_sign i413 i414)))))))))))

abbrev shared_expr_Classification095_14 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := ((c3_sign ≤ (0 : Int)) ∨ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2042 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)) ∨ (¬ (formula_2040 c3_node c3_sign r1_node r1_sign)) ∨ (¬ (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign)) ∨ (¬ (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign)))
abbrev formula_2551 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification095_14 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)

-- Checked replay of lemma.
theorem replay_6208 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2551 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6207 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))

theorem propositional_2229 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6209 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign) ∨ (r1_sign ≥ (1 : Int))) := by
  exact (propositional_2229 ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6210 (r1_sign : Int) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i377 : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))) : (¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) := by
  exact (Or.elim (replay_3536 r1_sign) (fun l0 => (False.elim (l0 i209))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_5709 r1_sign i377)))))))

-- Checked replay of unit-resolution.
theorem replay_6211 (r1_sign : Int) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i377 : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))) : (r1_sign ≤ (0 : Int)) := by
  exact (Or.elim (replay_3530 r1_sign) (fun l0 => (False.elim ((replay_6210 r1_sign i209 i377) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6212 (r1_sign : Int) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i377 : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))) : (¬ (r1_sign ≥ (1 : Int))) := by
  exact (Or.elim (replay_3747 r1_sign) (fun l0 => (False.elim (l0 (replay_6211 r1_sign i209 i377)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6213 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i377 : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))) : (formula_2037 c3_node c3_sign h r1_depth r1_node r1_sign) := by
  exact (Or.elim (replay_6209 c3_node c3_sign h r1_depth r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim ((replay_6212 r1_sign i209 i377) t0))))

theorem propositional_2230 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6214 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) : ((formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign) ∨ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
  exact (propositional_2230 ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6215 (c3_node c3_sign h r1_depth r1_node r1_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i233 : (formula_6 h r1_depth r1_sign)) (i377 : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))) : (formula_2036 c3_node c3_sign h r1_depth r1_node r1_sign) := by
  exact (Or.elim (replay_6214 c3_node c3_sign h r1_depth r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t105))))))))))))))))))) (fun t0 => (False.elim ((replay_5711 h r1_depth r1_sign i232 i233 i377) t0))))

theorem propositional_2231 (p0 p1 p2 p3 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6216 (c3_node c3_sign r1_node r1_sign : Int) : ((formula_2040 c3_node c3_sign r1_node r1_sign) ∨ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) := by
  exact (propositional_2231 ((c3_node + ((-1 : Int) * (r1_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))

-- Checked replay of unit-resolution.
theorem replay_6217 (c3_node c3_sign r1_node r1_sign : Int) (i377 : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))) : (formula_2040 c3_node c3_sign r1_node r1_sign) := by
  exact (Or.elim (replay_6216 c3_node c3_sign r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim (i377 t0))))

-- Checked replay of unit-resolution.
theorem replay_6218 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) (i232 : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) (i8 : ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) (i233 : (formula_6 h r1_depth r1_sign)) (i382 : ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) (i413 : (¬ (c3_sign ≤ (0 : Int)))) (i209 : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) (i377 : (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))))) (i383 : (formula_2042 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)) : False := by
  exact (Or.elim (replay_6208 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim (i413 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i8))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i382))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i383))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_6217 c3_node c3_sign r1_node r1_sign i377)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_6213 c3_node c3_sign h r1_depth r1_node r1_sign i209 i377)))) (fun t5 => (False.elim (t5 (replay_6215 c3_node c3_sign h r1_depth r1_node r1_sign i232 i233 i377)))))))))))))))

abbrev shared_expr_Classification095_15 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2042 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)) ∨ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (c3_sign ≤ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_6 h r1_depth r1_sign)) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))))
abbrev formula_2552 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : Prop := (shared_expr_Classification095_15 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign)

-- Checked replay of lemma.
theorem replay_6219 (c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign : Int) : (formula_2552 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6218 c3_depth c3_kind c3_node c3_sign h r1_depth r1_kind r1_node r1_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))))

-- Checked replay of th-lemma.
theorem replay_6220 (c3_sign : Int) : ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_2232 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6221 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : ((formula_2516 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) ∨ ((¬ (formula_2514 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2515 c3_node c3_sign r3_node r3_sign)))) := by
  exact (propositional_2232 ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((¬ (formula_2514 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2515 c3_node c3_sign r3_node r3_sign))))

abbrev shared_expr_Classification095_16 (c3_node c3_sign r3_node r3_sign : Int) : Prop := ((¬ ((¬ (formula_2514 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2515 c3_node c3_sign r3_node r3_sign)))) ∨ (¬ (formula_2514 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2515 c3_node c3_sign r3_node r3_sign)))
abbrev formula_2553 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (shared_expr_Classification095_16 c3_node c3_sign r3_node r3_sign)

theorem propositional_2233 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6222 (c3_node c3_sign r3_node r3_sign : Int) : (formula_2553 c3_node c3_sign r3_node r3_sign) := by
  exact (propositional_2233 (formula_2514 c3_node c3_sign r3_node r3_sign) (formula_2515 c3_node c3_sign r3_node r3_sign))

theorem propositional_2234 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6223 (c3_node c3_sign r3_node r3_sign : Int) : ((formula_2515 c3_node c3_sign r3_node r3_sign) ∨ (c3_sign ≥ (1 : Int))) := by
  exact (propositional_2234 ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6224 (c3_node c3_sign r3_node r3_sign : Int) (i417 : (¬ (c3_sign ≥ (1 : Int)))) : (formula_2515 c3_node c3_sign r3_node r3_sign) := by
  exact (Or.elim (replay_6223 c3_node c3_sign r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim (i417 t0))))

-- Checked replay of unit-resolution.
theorem replay_6225 (c3_node c3_sign r3_node r3_sign : Int) (i417 : (¬ (c3_sign ≥ (1 : Int)))) (i418 : (formula_2514 c3_node c3_sign r3_node r3_sign)) : (¬ ((¬ (formula_2514 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2515 c3_node c3_sign r3_node r3_sign)))) := by
  exact (Or.elim (replay_6222 c3_node c3_sign r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i418))) (fun t1 => (False.elim (t1 (replay_6224 c3_node c3_sign r3_node r3_sign i417)))))))

-- Checked replay of unit-resolution.
theorem replay_6226 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) (i417 : (¬ (c3_sign ≥ (1 : Int)))) (i418 : (formula_2514 c3_node c3_sign r3_node r3_sign)) : (formula_2516 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_6221 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6225 c3_node c3_sign r3_node r3_sign i417 i418) t0))))

abbrev shared_expr_Classification095_17 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2512 c3_node c3_sign h r3_depth r3_node r3_sign))) ∨ (formula_2512 c3_node c3_sign h r3_depth r3_node r3_sign))
abbrev formula_2554 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification095_17 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)

theorem propositional_2235 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6227 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : (formula_2554 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_2235 ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) (formula_2512 c3_node c3_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Classification095_18 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (formula_2512 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_2510 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2511 c3_node c3_sign h r3_depth r3_node r3_sign)))
abbrev formula_2555 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Classification095_18 c3_node c3_sign h r3_depth r3_node r3_sign)

theorem propositional_2236 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6228 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : (formula_2555 c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_2236 (formula_2510 c3_node c3_sign h r3_depth r3_node r3_sign) ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) (formula_2511 c3_node c3_sign h r3_depth r3_node r3_sign))

theorem propositional_2237 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p5) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6229 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : ((formula_2511 c3_node c3_sign h r3_depth r3_node r3_sign) ∨ (c3_sign ≥ (1 : Int))) := by
  exact (propositional_2237 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6230 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i417 : (¬ (c3_sign ≥ (1 : Int)))) : (formula_2511 c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_6229 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (i417 t0))))

-- Checked replay of unit-resolution.
theorem replay_6231 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i417 : (¬ (c3_sign ≥ (1 : Int)))) (i420 : (formula_2510 c3_node c3_sign h r3_depth r3_node r3_sign)) (i419 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) : (¬ (formula_2512 c3_node c3_sign h r3_depth r3_node r3_sign)) := by
  exact (Or.elim (replay_6228 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i420))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i419))) (fun t2 => (False.elim (t2 (replay_6230 c3_node c3_sign h r3_depth r3_node r3_sign i417)))))))))

-- Checked replay of unit-resolution.
theorem replay_6232 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i417 : (¬ (c3_sign ≥ (1 : Int)))) (i420 : (formula_2510 c3_node c3_sign h r3_depth r3_node r3_sign)) (i419 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) : ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2512 c3_node c3_sign h r3_depth r3_node r3_sign))) := by
  exact (Or.elim (replay_6227 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6231 c3_node c3_sign h r3_depth r3_node r3_sign i417 i420 i419) t0))))

-- Checked replay of unit-resolution.
theorem replay_6233 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) (i148 : ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))))) (i382 : ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) (i417 : (¬ (c3_sign ≥ (1 : Int)))) (i420 : (formula_2510 c3_node c3_sign h r3_depth r3_node r3_sign)) (i419 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i418 : (formula_2514 c3_node c3_sign r3_node r3_sign)) (i397 : (formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) : False := by
  exact (Or.elim (replay_5962 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) (fun l0 => (False.elim (l0 i397))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i148))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i382))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6232 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i417 i420 i419)))) (fun t3 => (False.elim (t3 (replay_6226 c3_depth c3_node c3_sign r3_depth r3_node r3_sign i417 i418)))))))))))

abbrev shared_expr_Classification095_19 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := ((c3_sign ≥ (1 : Int)) ∨ (¬ ((¬ (r3_kind ≤ (2 : Int))) ∨ (¬ (r3_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2517 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)) ∨ (¬ (formula_2514 c3_node c3_sign r3_node r3_sign)) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2510 c3_node c3_sign h r3_depth r3_node r3_sign)))
abbrev formula_2556 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Classification095_19 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_6234 (c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign : Int) : (formula_2556 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6233 c3_depth c3_kind c3_node c3_sign h r3_depth r3_kind r3_node r3_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))))

theorem propositional_2238 (p0 p1 p2 p3 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6235 (c3_node c3_sign r3_node r3_sign : Int) : ((formula_2514 c3_node c3_sign r3_node r3_sign) ∨ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) := by
  exact (propositional_2238 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Classification095_20 (r3_sign : Int) : Prop := ((¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))
abbrev formula_2557 (r3_sign : Int) : Prop := (shared_expr_Classification095_20 r3_sign)

theorem propositional_2239 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6236 (r3_sign : Int) : (formula_2557 r3_sign) := by
  exact (propositional_2239 ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))) ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))

theorem propositional_2240 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6237 (r3_sign : Int) : (((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))) ∨ (r3_sign ≥ (2 : Int))) := by
  exact (propositional_2240 (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_6238 (r3_sign : Int) : ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_2241 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6239 (r3_sign : Int) : (((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) ∨ (r3_sign ≤ (1 : Int))) := by
  exact (propositional_2241 (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)))

abbrev shared_expr_Classification095_21 (r3_sign : Int) : Prop := ((¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))))
abbrev formula_2558 (r3_sign : Int) : Prop := (shared_expr_Classification095_21 r3_sign)

theorem propositional_2242 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6240 (r3_sign : Int) : (formula_2558 r3_sign) := by
  exact (propositional_2242 ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))) ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))))

theorem propositional_2243 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6241 (r3_sign : Int) : (((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int)))) ∨ (r3_sign ≤ (0 : Int))) := by
  exact (propositional_2243 (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_6242 (r3_sign : Int) : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Classification095_22 (r3_sign : Int) : Prop := ((¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))
abbrev formula_2559 (r3_sign : Int) : Prop := (shared_expr_Classification095_22 r3_sign)

theorem propositional_2244 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6243 (r3_sign : Int) : (formula_2559 r3_sign) := by
  exact (propositional_2244 ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))

theorem propositional_2245 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6244 (r3_sign : Int) : (((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) ∨ (r3_sign ≥ (1 : Int))) := by
  exact (propositional_2245 (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)))

end H4Formal.Generated.Classification
