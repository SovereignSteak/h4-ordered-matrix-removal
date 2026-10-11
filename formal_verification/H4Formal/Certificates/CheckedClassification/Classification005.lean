import H4Formal.Certificates.CheckedClassification.Classification004

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev formula_161 (c0_level c2_level r2_depth r3_depth : Int) : Prop := ((¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ∨ ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_226 (c0_level c2_level r2_depth r3_depth : Int) : (formula_161 c0_level c2_level r2_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_227 (c2_level r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev formula_162 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))

theorem propositional_125 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_228 (c2_level r3_depth r3_kind r3_sign : Int) : ((formula_162 c2_level r3_depth r3_kind r3_sign) ∨ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))) := by
  exact (propositional_125 (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

abbrev formula_163 (c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))

abbrev formula_164 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ (formula_162 c2_level r3_depth r3_kind r3_sign))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_163 c2_level r3_depth r3_kind r3_sign))))

theorem propositional_126 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_229 (c2_group c2_level r3_depth r3_kind r3_sign : Int) : ((¬ (formula_164 c2_group c2_level r3_depth r3_kind r3_sign)) ∨ (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∨ (¬ (formula_162 c2_level r3_depth r3_kind r3_sign))) := by
  exact (propositional_126 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (formula_162 c2_level r3_depth r3_kind r3_sign) (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r3_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

-- Checked replay of th-lemma.
theorem replay_230 (r2_node : Int) : ((¬ ((r2_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r2_node % (2 : Int)) ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev formula_165 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))

theorem propositional_127 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_231 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_165 c2_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_node % (2 : Int)) ≥ (1 : Int))) := by
  exact (propositional_127 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

abbrev formula_166 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_165 c2_level r2_depth r2_kind r2_node r2_sign))))

theorem propositional_128 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_232 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_166 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∨ (¬ (formula_165 c2_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_128 ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_165 c2_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_129 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_233 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_166 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_166 c2_group c2_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_129 (c2_mode ≤ (5 : Int)) (c2_mode ≥ (5 : Int)) (formula_166 c2_group c2_level r2_depth r2_kind r2_node r2_sign))

abbrev formula_167 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))

abbrev formula_168 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))

abbrev formula_169 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ (formula_167 c2_level r2_depth r2_kind r2_sign))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_168 c2_level r2_depth r2_kind r2_sign))))

abbrev formula_170 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))

abbrev formula_171 (c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))

abbrev formula_172 (c2_group c2_level r2_depth r2_kind r2_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ (formula_170 c2_level r2_depth r2_kind r2_sign))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_171 c2_level r2_depth r2_kind r2_sign))))

abbrev formula_173 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))

abbrev formula_174 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_173 c2_level r2_depth r2_kind r2_node r2_sign))))

abbrev formula_175 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))

abbrev formula_176 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_175 c2_level r2_depth r2_kind r2_node r2_sign))))

abbrev formula_177 (c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int))))

abbrev formula_178 (c2_group c2_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∧ (¬ (formula_177 c2_level r2_depth r2_kind r2_node r2_sign))))

abbrev formula_179 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_169 c2_group c2_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_172 c2_group c2_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_174 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_176 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_178 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_166 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))))

abbrev formula_180 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_169 c2_group c2_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_172 c2_group c2_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_174 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_176 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_178 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_166 c2_group c2_level r2_depth r2_kind r2_node r2_sign)))))

theorem propositional_130 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_234 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (formula_180 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) := by
  exact (propositional_130 ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_169 c2_group c2_level r2_depth r2_kind r2_sign))) ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_172 c2_group c2_level r2_depth r2_kind r2_sign))) ((¬ (c2_mode ≤ (2 : Int))) ∨ (¬ (c2_mode ≥ (2 : Int))) ∨ (¬ (formula_174 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_176 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_178 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_166 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))

theorem propositional_131 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ ((¬ ((¬ p8) ∨ (¬ p9))) ∨ (¬ ((¬ p10) ∨ (¬ p11))))) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_235 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c2_mode ≤ (4 : Int))) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (¬ (formula_178 c2_group c2_level r2_depth r2_kind r2_node r2_sign))) ∨ (c2_mode ≤ (4 : Int))) := by
  exact (propositional_131 (c2_mode ≤ (4 : Int)) (c2_mode ≥ (4 : Int)) (c2_group ≤ (1 : Int)) (c2_group ≥ (1 : Int)) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_236 (c0_mode c2_mode : Int) : ((c0_mode ≤ (3 : Int)) ∨ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ∨ (¬ (c2_mode ≤ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_237 (c0_mode : Int) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_132 (p0 p1 : Prop) : ((¬ (p0 ↔ p1)) ∨ p0 ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_238 (c0_mode c2_mode : Int) : ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∨ (c0_mode ≥ (4 : Int)) ∨ (¬ (c2_mode ≥ (4 : Int)))) := by
  exact (propositional_132 (c0_mode ≥ (4 : Int)) (c2_mode ≥ (4 : Int)))

abbrev formula_181 (c0_group c0_mode c2_group c2_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ∧ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ∧ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)))))

abbrev formula_182 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ∧ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))))) ∧ (formula_181 c0_group c0_mode c2_group c2_mode)))

abbrev formula_183 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : Prop := (¬ ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_182 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))

theorem propositional_133 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ p2)) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ ((((¬ p3) ∨ (¬ p4)) ∧ (¬ p4)) ∨ ((¬ ((¬ p3) ∨ (¬ p4))) ∧ (¬ p5)))))) ∨ ((¬ p0) ∧ p6))) ∨ p0 ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_239 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : ((formula_183 c0_group c0_level c0_mode c2_group c2_level c2_mode) ∨ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∨ (c0_mode ≥ (4 : Int))) := by
  exact (propositional_133 ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int)) (c0_mode ≥ (4 : Int)))

-- Checked replay of unit-resolution.
theorem replay_240 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) (i27 : ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_182 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))) (i26 : (¬ (c0_mode ≥ (4 : Int)))) : ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_239 c0_group c0_level c0_mode c2_group c2_level c2_mode) (fun l0 => (False.elim (l0 i27))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (i26 t1))))))

-- Checked replay of unit-resolution.
theorem replay_241 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) (i28 : (c2_mode ≥ (4 : Int))) (i27 : ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_182 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))) (i26 : (¬ (c0_mode ≥ (4 : Int)))) : False := by
  exact (Or.elim (replay_238 c0_mode c2_mode) (fun l0 => (False.elim (l0 (replay_240 c0_group c0_level c0_mode c2_group c2_level c2_mode i27 i26)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i26 l1))) (fun t1 => (False.elim (t1 i28))))))

-- Checked replay of lemma.
theorem replay_242 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : ((c0_mode ≥ (4 : Int)) ∨ (¬ (c2_mode ≥ (4 : Int))) ∨ (formula_183 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_241 c0_group c0_level c0_mode c2_group c2_level c2_mode (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))) (fun q => nc (Or.inl q)))

abbrev formula_184 (c0_level c2_level r1_depth r2_depth : Int) : Prop := ((¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

-- Checked replay of th-lemma.
theorem replay_243 (c0_level c2_level r1_depth r2_depth : Int) : (formula_184 c0_level c2_level r1_depth r2_depth) := by
  classical
  first | omega | grind (splits := 40)

abbrev formula_185 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))

abbrev formula_186 (c2_level r1_depth r1_kind r1_sign : Int) : Prop := ((¬ (formula_185 c2_level r1_depth r1_kind r1_sign)) ∨ (¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))))

theorem propositional_134 (p0 p1 p2 p3 p4 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_244 (c2_level r1_depth r1_kind r1_sign : Int) : (formula_186 c2_level r1_depth r1_kind r1_sign) := by
  exact (propositional_134 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int)))

abbrev formula_187 (c0_level c2_level r1_depth r2_depth : Int) : Prop := (((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))

-- Checked replay of th-lemma.
theorem replay_245 (c0_level c2_level r1_depth r2_depth : Int) : (formula_187 c0_level c2_level r1_depth r2_depth) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_135 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_246 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((formula_132 c0_level r1_depth r1_kind r1_node r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  exact (propositional_135 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≥ (1 : Int)))

theorem propositional_136 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_247 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_132 c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (propositional_136 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (formula_132 c0_level r1_depth r1_kind r1_node r1_sign))

theorem propositional_137 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_248 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (c0_mode ≤ (4 : Int))) := by
  exact (propositional_137 (c0_mode ≤ (4 : Int)) (c0_mode ≥ (4 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_249 (c0_mode : Int) : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_138 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_250 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_151 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (c0_mode ≥ (5 : Int))) := by
  exact (propositional_138 (c0_mode ≤ (5 : Int)) (c0_mode ≥ (5 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)))

theorem propositional_139 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_251 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((formula_130 c0_level r1_depth r1_kind r1_node r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  exact (propositional_139 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

theorem propositional_140 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_252 (c0_group c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_130 c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (propositional_140 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (formula_130 c0_level r1_depth r1_kind r1_node r1_sign))

theorem propositional_141 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_253 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (c0_mode ≥ (5 : Int))) := by
  exact (propositional_141 (c0_mode ≤ (5 : Int)) (c0_mode ≥ (5 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≥ (1 : Int)))

theorem propositional_142 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_254 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (c0_mode ≤ (4 : Int))) := by
  exact (propositional_142 (c0_mode ≤ (4 : Int)) (c0_mode ≥ (4 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_255 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (c0_mode ≤ (4 : Int)) := by
  exact (Or.elim (replay_254 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (i29 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_256 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (¬ (c0_mode ≥ (5 : Int))) := by
  exact (Or.elim (replay_249 c0_mode) (fun l0 => (False.elim (l0 (replay_255 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i29)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_257 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_133 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) := by
  exact (Or.elim (replay_253 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_256 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i29) t0))))

-- Checked replay of unit-resolution.
theorem replay_258 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) := by
  exact (Or.elim (replay_183 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim (l0 i23))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i22))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i21))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i19))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i20))) (fun t4 => (Or.elim t4 (fun l5 => l5) (fun t5 => (False.elim (t5 (replay_257 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i29)))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_259 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (formula_131 c0_group c0_level r1_depth r1_kind r1_node r1_sign) := by
  exact (Or.elim (replay_188 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_258 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i22 i21 i19 i20 i23 i29) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_260 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (¬ (formula_130 c0_level r1_depth r1_kind r1_node r1_sign)) := by
  exact (Or.elim (replay_252 c0_group c0_level r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim (l0 (replay_259 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i22 i21 i19 i20 i23 i29)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i30 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_261 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_251 c0_level r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_260 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29) l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_262 (c0_level r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_143 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_263 (c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_148 c0_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_143 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)))

theorem propositional_144 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_264 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_148 c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_144 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_148 c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_145 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_265 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_145 (c0_mode ≤ (4 : Int)) (c0_mode ≥ (4 : Int)) (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))

-- Checked replay of unit-resolution.
theorem replay_266 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_265 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (i29 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_267 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (¬ (formula_148 c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_264 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_266 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i29)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i30 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_268 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_263 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim ((replay_267 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i30 i29) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_269 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) := by
  exact (Or.elim (replay_262 c0_level r2_depth) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_268 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i30 i29)))))

-- Checked replay of unit-resolution.
theorem replay_270 (c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) (i31 : ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) : ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)) := by
  exact (Or.elim (replay_245 c0_level c2_level r1_depth r2_depth) (fun l0 => (False.elim ((replay_269 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i30 i29) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i31))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_261 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29)))) (fun t2 => t2))))))

theorem propositional_146 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_271 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((formula_130 c0_level r1_depth r1_kind r1_node r1_sign) ∨ (r1_kind ≤ (1 : Int))) := by
  exact (propositional_146 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_272 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (r1_kind ≤ (1 : Int)) := by
  exact (Or.elim (replay_271 c0_level r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_260 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29) l0))) (fun t0 => t0))

theorem propositional_147 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_273 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((formula_130 c0_level r1_depth r1_kind r1_node r1_sign) ∨ (r1_kind ≥ (1 : Int))) := by
  exact (propositional_147 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_274 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (r1_kind ≥ (1 : Int)) := by
  exact (Or.elim (replay_273 c0_level r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_260 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29) l0))) (fun t0 => t0))

theorem propositional_148 (p0 p1 p2 p3 p4 p5 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p4) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_275 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((formula_130 c0_level r1_depth r1_kind r1_node r1_sign) ∨ ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))))) := by
  exact (propositional_148 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_276 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) := by
  exact (Or.elim (replay_275 c0_level r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_260 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_277 (c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i32 : (formula_185 c2_level r1_depth r1_kind r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) (i31 : ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) : (¬ ((r1_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) := by
  exact (Or.elim (replay_244 c2_level r1_depth r1_kind r1_sign) (fun l0 => (False.elim (l0 i32))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_272 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_274 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_276 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_270 c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29 i31)))) (fun t4 => t4))))))))))

-- Checked replay of th-lemma.
theorem replay_278 (c0_level r1_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_149 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_279 (c0_level r1_depth r1_kind r1_node r1_sign : Int) : ((formula_130 c0_level r1_depth r1_kind r1_node r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  exact (propositional_149 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_280 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_279 c0_level r1_depth r1_kind r1_node r1_sign) (fun l0 => (False.elim ((replay_260 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_281 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) := by
  exact (Or.elim (replay_278 c0_level r1_depth) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_280 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29)))))

theorem propositional_150 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_282 (c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((formula_148 c0_level r2_depth r2_kind r2_node r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  exact (propositional_150 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_283 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_282 c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim ((replay_267 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i30 i29) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_284 (c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i22 : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) (i21 : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) (i19 : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i20 : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) (i23 : (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) (i32 : (formula_185 c2_level r1_depth r1_kind r1_sign)) (i29 : (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))))) (i31 : ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) (i33 : ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) : False := by
  exact (Or.elim (replay_243 c0_level c2_level r1_depth r2_depth) (fun l0 => (False.elim (l0 (replay_283 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign i30 i29)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i33))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim ((replay_281 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i29) l2))) (fun t2 => (False.elim ((replay_277 c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign i30 i22 i21 i19 i20 i23 i32 i29 i31) t2))))))))

abbrev formula_188 (c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : Prop := (((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_149 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) ∨ (¬ (formula_185 c2_level r1_depth r1_kind r1_sign)) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_127 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ (formula_134 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)))

-- Checked replay of lemma.
theorem replay_285 (c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign : Int) : (formula_188 c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_284 c0_group c0_level c0_mode c2_level r1_depth r1_kind r1_node r1_sign r2_depth r2_kind r2_node r2_sign (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

theorem propositional_151 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_286 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : (((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_122 c0_group c0_level r1_depth r1_kind r1_sign))) ∨ (c0_mode ≤ (0 : Int))) := by
  exact (propositional_151 (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_287 (c0_mode : Int) : ((c0_mode ≥ (1 : Int)) ∨ (¬ (c0_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_288 (c0_mode : Int) : ((c0_mode ≥ (2 : Int)) ∨ (¬ (c0_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_289 (c0_mode : Int) : ((c0_mode ≥ (3 : Int)) ∨ (¬ (c0_mode ≥ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev formula_189 (c0_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))))

abbrev formula_190 (c0_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (formula_189 c0_level r3_depth r3_kind r3_sign)) ∨ (¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))))

theorem propositional_152 (p0 p1 p2 p3 p4 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_290 (c0_level r3_depth r3_kind r3_sign : Int) : (formula_190 c0_level r3_depth r3_kind r3_sign) := by
  exact (propositional_152 (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))))

abbrev formula_191 (c0_level c2_level r2_depth r3_depth : Int) : Prop := ((¬ ((r2_depth + ((-1 : Int) * c2_level)) ≥ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_291 (c0_level c2_level r2_depth r3_depth : Int) : (formula_191 c0_level c2_level r2_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_153 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_292 (c0_level r2_depth r2_kind r2_sign : Int) : ((formula_141 c0_level r2_depth r2_kind r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  exact (propositional_153 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

theorem propositional_154 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_293 (c0_group c0_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ (formula_141 c0_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_154 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (formula_141 c0_level r2_depth r2_kind r2_sign) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))))

theorem propositional_155 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_294 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))) ∨ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign)) := by
  exact (propositional_155 (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))

abbrev formula_192 (c0_level c2_level r1_depth r2_depth : Int) : Prop := ((¬ ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) ∨ ((r1_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int)))

-- Checked replay of th-lemma.
theorem replay_295 (c0_level c2_level r1_depth r2_depth : Int) : (formula_192 c0_level c2_level r1_depth r2_depth) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_156 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_296 (c0_level r1_depth r1_kind r1_sign : Int) : ((formula_124 c0_level r1_depth r1_kind r1_sign) ∨ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) := by
  exact (propositional_156 (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)))

theorem propositional_157 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)))) ∨ ((¬ p0) ∧ (¬ p6)))) ∨ p0 ∨ (¬ p6)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_297 (c0_group c0_level r1_depth r1_kind r1_sign : Int) : ((¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_124 c0_level r1_depth r1_kind r1_sign))) := by
  exact (propositional_157 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))))) (formula_124 c0_level r1_depth r1_kind r1_sign))

theorem propositional_158 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_298 (c0_group c0_level c0_mode r1_depth r1_kind r1_sign : Int) : (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign))) ∨ (formula_125 c0_group c0_level r1_depth r1_kind r1_sign)) := by
  exact (propositional_158 (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (formula_125 c0_group c0_level r1_depth r1_kind r1_sign))

theorem propositional_159 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p6) ∨ (¬ p7) ∨ (¬ ((¬ ((¬ p8) ∨ (¬ p9))) ∨ (¬ ((¬ p10) ∨ (¬ p11))))) ∨ (¬ p12) ∨ (¬ p13) ∨ (¬ p14))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_299 (c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign : Int) : (((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_129 c0_group c0_level r1_depth r1_kind r1_node r1_sign))) ∨ (c0_mode ≥ (3 : Int))) := by
  exact (propositional_159 (c0_mode ≤ (3 : Int)) (c0_mode ≥ (3 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r1_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r1_node % (2 : Int)) ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_300 (c0_mode : Int) : ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_160 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p8))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_301 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) : (((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_143 c0_group c0_level r2_depth r2_kind r2_sign))) ∨ (c0_mode ≤ (1 : Int))) := by
  exact (propositional_160 (c0_mode ≤ (1 : Int)) (c0_mode ≥ (1 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)))

theorem propositional_161 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_302 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_147 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_146 c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_161 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_146 c0_level r2_depth r2_kind r2_node r2_sign))

-- Checked replay of unit-resolution.
theorem replay_303 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i34 : (formula_146 c0_level r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_147 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_302 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i30 l1))) (fun t1 => (False.elim (t1 i34))))))

-- Checked replay of unit-resolution.
theorem replay_304 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) (i30 : (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))))) (i34 : (formula_146 c0_level r2_depth r2_kind r2_node r2_sign)) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_147 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_199 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_303 c0_group c0_level r2_depth r2_kind r2_node r2_sign i30 i34) t0))))

theorem propositional_162 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_305 (c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign : Int) : (((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_145 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) ∨ (formula_145 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (propositional_162 (c0_mode ≤ (2 : Int)) (c0_mode ≥ (2 : Int)) (formula_145 c0_group c0_level r2_depth r2_kind r2_node r2_sign))

theorem propositional_163 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ ((¬ p1) ∨ (¬ p2)))) ∨ ((¬ p0) ∧ (¬ p3)))) ∨ p0 ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_306 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_145 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ∨ (¬ (formula_144 c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (propositional_163 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (formula_144 c0_level r2_depth r2_kind r2_node r2_sign))

end H4Formal.Generated.Classification
