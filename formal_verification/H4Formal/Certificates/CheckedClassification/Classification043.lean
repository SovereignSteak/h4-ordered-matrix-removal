import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedClassification.Classification042

namespace H4Formal.Generated.Classification

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

-- Checked replay of unit-resolution.
theorem replay_2333 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i100 : (formula_786 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i77 : (formula_591 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i71 : (formula_574 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i65 : (formula_505 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i133 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i165 : (c2_mode ≤ (0 : Int))) (i74 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i50 : (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (r2_kind ≥ (2 : Int))) := by
  exact (Or.elim (replay_112 r2_kind) (fun l0 => (False.elim (l0 (replay_2332 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i100 i77 i71 i65 i133 i165 i74 i50)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2334 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i100 : (formula_786 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i77 : (formula_591 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i71 : (formula_574 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i65 : (formula_505 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i133 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i165 : (c2_mode ≤ (0 : Int))) (i74 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i50 : (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (formula_73 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) := by
  exact (Or.elim (replay_111 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim ((replay_2333 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_kind r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i100 i77 i71 i65 i133 i165 i74 i50) t0))))

-- Checked replay of unit-resolution.
theorem replay_2335 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i12 : (formula_67 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i100 : (formula_786 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i77 : (formula_591 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i71 : (formula_574 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i65 : (formula_505 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i133 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i165 : (c2_mode ≤ (0 : Int))) (i74 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i50 : (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (formula_62 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) := by
  exact (Or.elim (replay_110 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i12) (fun l0 => (False.elim (l0 (replay_2334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i100 i77 i71 i65 i133 i165 i74 i50)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_2330 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i100 i77 i71 i65 i133 i165 i74 i50)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_2336 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i12 : (formula_67 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i100 : (formula_786 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i77 : (formula_591 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i71 : (formula_574 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i65 : (formula_505 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i133 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i165 : (c2_mode ≤ (0 : Int))) (i74 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i50 : (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_1569 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) (fun l0 => (False.elim ((replay_2335 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i12 i100 i77 i71 i65 i133 i165 i74 i50) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2337 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i12 : (formula_67 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i100 : (formula_786 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i77 : (formula_591 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i71 : (formula_574 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i65 : (formula_505 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i133 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i165 : (c2_mode ≤ (0 : Int))) (i74 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i50 : (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) (i173 : ((h + ((-1 : Int) * c1_level)) ≤ (0 : Int))) : ((r2_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_1568 c1_level h r2_depth) (fun l0 => (False.elim (l0 i173))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_2336 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i12 i100 i77 i71 i65 i133 i165 i74 i50)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_2338 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i131 : (formula_1034 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) (i12 : (formula_67 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i100 : (formula_786 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i77 : (formula_591 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i71 : (formula_574 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i101 : (formula_812 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i85 : (formula_738 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i65 : (formula_505 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i63 : ((formula_414 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) (i62 : ((formula_279 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) (i134 : ((formula_1114 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ False)) (i136 : ((formula_1206 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i147 : ((formula_1334 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) (i84 : ((formula_647 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) (i133 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i165 : (c2_mode ≤ (0 : Int))) (i74 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i50 : (formula_179 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) : ((r2_depth + ((-1 : Int) * c1_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_1757 c1_level h r2_depth) (fun l0 => (False.elim (l0 (replay_1763 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h i77 i71 i65 i74)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_2326 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i131 i12 i100 i77 i71 i101 i85 i65 i63 i62 i134 i136 i147 i84 i133 i165 i74 i50)))) (fun t1 => t1))))

abbrev shared_expr_Classification043_0 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_764 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1439 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (shared_expr_Classification043_0 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)

abbrev shared_expr_Classification043_1 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((¬ (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ∨ (¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_764 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1440 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (shared_expr_Classification043_1 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)

theorem propositional_1191 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ p2)) ∨ (¬ p0) ∨ (¬ p1) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2339 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1440 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := by
  exact (propositional_1191 (c1_kind ≤ (0 : Int)) (c1_kind ≥ (0 : Int)) ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_764 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))

abbrev shared_expr_Classification043_2 (c0_node c1_node : Int) : Prop := (((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Classification043_3 (c0_node c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev formula_1441 (c0_node c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_2 c0_node c1_node) ∨ (shared_expr_Classification043_3 c0_node c1_node c1_sign))

abbrev shared_expr_Classification043_4 (c0_node c1_node : Int) : Prop := (((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Classification043_5 (c0_node c0_sign c1_node : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))))
abbrev formula_1442 (c0_node c0_sign c1_node : Int) : Prop := ((shared_expr_Classification043_4 c0_node c1_node) ∨ (shared_expr_Classification043_5 c0_node c0_sign c1_node))

abbrev shared_expr_Classification043_6 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int))) ∨ (formula_1441 c0_node c1_node c1_sign)))
abbrev shared_expr_Classification043_7 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_6 c0_depth c0_node c1_depth c1_node c1_sign) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int))))) ∧ (formula_1442 c0_node c0_sign c1_node)))
abbrev formula_1443 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_7 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_8 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((¬ ((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev shared_expr_Classification043_9 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∨ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))) ∨ (shared_expr_Classification043_8 c0_node c0_sign c1_node c1_sign))
abbrev formula_1444 (c0_node c0_sign c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_9 c0_node c0_sign c1_node c1_sign)

abbrev shared_expr_Classification043_10 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ∧ (formula_1443 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ∧ (formula_1444 c0_node c0_sign c1_node c1_sign)))
abbrev formula_1445 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_10 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_11 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int)))) ∧ (¬ ((¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ∨ (¬ (formula_1445 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))))) ∨ ((¬ ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))))
abbrev formula_1446 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_11 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Classification043_12 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∧ (¬ ((¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ∨ (¬ (formula_1446 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))))
abbrev shared_expr_Classification043_13 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_12 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ∨ ((¬ ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))))) ∧ (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)))
abbrev formula_1447 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_13 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Classification043_14 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) ∨ (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (¬ (formula_1447 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)))
abbrev formula_1448 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_14 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem propositional_1192 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Prop) : (p0 ∨ p1 ∨ (¬ ((p0 ∧ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((((¬ p4) ∨ (¬ p5)) ∧ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((((¬ p8) ∨ (¬ p9)) ∧ ((((¬ p10) ∨ (¬ p11)) ∧ ((¬ p12) ∨ (¬ p13) ∨ ((((¬ p14) ∨ (¬ p15)) ∧ (¬ p14)) ∨ ((¬ ((¬ p14) ∨ (¬ p15))) ∧ (¬ ((¬ p16) ∨ (¬ p17))))))) ∨ ((¬ ((¬ p10) ∨ (¬ p11))) ∧ ((((¬ p18) ∨ (¬ p19)) ∧ (¬ p19)) ∨ ((¬ ((¬ p18) ∨ (¬ p19))) ∧ (¬ ((¬ p20) ∨ (¬ p21)))))))) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ ((((¬ p22) ∨ (¬ p23)) ∧ (¬ p23)) ∨ ((¬ ((¬ p22) ∨ (¬ p23))) ∧ (¬ ((¬ p20) ∨ (¬ p21) ∨ (¬ p16) ∨ (¬ p17))))))))))) ∨ ((¬ ((¬ p4) ∨ (¬ p5))) ∧ (¬ ((¬ p24) ∨ (¬ p25))))))))) ∨ ((¬ p0) ∧ p1)))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2340 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1448 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact (propositional_1192 ((¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int)))) (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (c1_kind ≤ (0 : Int)) (c1_kind ≥ (0 : Int)) (c0_kind ≤ (2 : Int)) (c0_kind ≥ (2 : Int)) (c1_kind ≤ (2 : Int)) (c1_kind ≥ (2 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (-1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≥ (0 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)) ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) (c1_kind ≤ (1 : Int)) (c1_kind ≥ (1 : Int)))

abbrev shared_expr_Classification043_15 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((¬ (¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))))) ∧ (((c0_level ≠ c1_level) ∧ (c0_level < c1_level)) ∨ ((¬ (c0_level ≠ c1_level)) ∧ (((c0_mode ≠ c1_mode) ∧ (c0_mode < c1_mode)) ∨ ((¬ (c0_mode ≠ c1_mode)) ∧ (c0_group < c1_group))))))
abbrev formula_1449 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))) ∨ (shared_expr_Classification043_15 c0_group c0_level c0_mode c1_group c1_level c1_mode))

abbrev shared_expr_Classification043_16 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((((c1_depth + (1 : Int)) = c0_depth) ∧ (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ ((c0_node / (2 : Int)) < c1_node)))) ∨ ((¬ ((c1_depth + (1 : Int)) = c0_depth)) ∧ True))
abbrev formula_1450 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_16 c0_depth c0_node c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_17 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((((c0_depth + (1 : Int)) = c1_depth) ∧ (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (c0_node < (c1_node / (2 : Int)))))) ∨ ((¬ ((c0_depth + (1 : Int)) = c1_depth)) ∧ (formula_1450 c0_depth c0_node c1_depth c1_node c1_sign)))
abbrev formula_1451 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_17 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_18 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = c1_depth) ∧ (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (c0_node < c1_node)))) ∨ ((¬ (c0_depth = c1_depth)) ∧ (formula_1451 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1452 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_18 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_19 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((c0_kind = (2 : Int)) ∧ (True ∧ (c1_kind = (1 : Int)))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ (((c1_kind = (2 : Int)) ∧ False) ∨ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1452 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1453 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_19 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Classification043_20 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ (((c1_kind = (0 : Int)) ∧ (formula_1449 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ (c1_kind = (0 : Int))) ∧ True))) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (((c1_kind = (0 : Int)) ∧ False) ∨ ((¬ (c1_kind = (0 : Int))) ∧ (formula_1453 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))))
abbrev formula_1454 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_20 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Classification043_21 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (((c0_level = c1_level) ∧ (((c0_mode = c1_mode) ∧ (¬ (c1_group ≤ c0_group))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ (c1_mode ≤ c0_mode))))) ∨ ((¬ (c0_level = c1_level)) ∧ (¬ (c1_level ≤ c0_level)))))
abbrev formula_1455 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((shared_expr_Classification043_21 c0_group c0_level c0_mode c1_group c1_level c1_mode) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))

abbrev shared_expr_Classification043_22 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (c0_depth = ((-1 : Int) + c1_depth))) ∧ ((¬ (c1_depth = ((-1 : Int) + c0_depth))) ∨ (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ (¬ (c1_node ≤ (c0_node / (2 : Int))))))))
abbrev shared_expr_Classification043_23 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = ((-1 : Int) + c1_depth)) ∧ (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (¬ ((c1_node / (2 : Int)) ≤ c0_node))))) ∨ (shared_expr_Classification043_22 c0_depth c0_node c1_depth c1_node c1_sign))
abbrev formula_1456 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_23 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_24 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = c1_depth) ∧ (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ (c1_node ≤ c0_node))))) ∨ ((¬ (c0_depth = c1_depth)) ∧ (formula_1456 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1457 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_24 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_25 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (c1_kind = (0 : Int))) ∧ (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1457 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1458 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_25 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Classification043_26 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ ((¬ (c1_kind = (0 : Int))) ∨ (formula_1455 c0_group c0_level c0_mode c1_group c1_level c1_mode))) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_1458 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
abbrev formula_1459 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_26 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Classification043_27 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((formula_1454 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
abbrev formula_1460 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_27 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem normalized_1193 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (True ∧ p10)) ∨ ((¬ p9) ∧ ((p11 ∧ False) ∨ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ p15))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((p18 ∧ ((p19 ∧ p20) ∨ ((¬ p19) ∧ p21))) ∨ ((¬ p18) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ ((p9 ∧ p10) ∨ ((¬ p9) ∧ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ (¬ (¬ p15))))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((¬ p18) ∨ ((p19 ∧ p20) ∨ ((¬ p19) ∧ (¬ (¬ p21)))))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4869 (c0_mode c1_mode : Int) : (¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_3411 c0_mode) (normalization_1824 c1_mode)))

theorem normalization_4870 (c0_level c1_level : Int) : (c0_level ≠ c1_level) ↔ (¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_4871 (c0_level c1_level : Int) : (c0_level < c1_level) ↔ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_4872 (c0_mode c1_mode : Int) : (c0_mode ≠ c1_mode) ↔ (¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_4873 (c0_mode c1_mode : Int) : (c0_mode < c1_mode) ↔ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_4874 (c0_group c1_group : Int) : (c0_group < c1_group) ↔ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Classification043_28 (c0_group c0_mode c1_group c1_mode : Int) : Prop := (((¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∧ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))))) ∧ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))))
theorem normalization_4875 (c0_group c0_mode c1_group c1_mode : Int) : (((c0_mode ≠ c1_mode) ∧ (c0_mode < c1_mode)) ∨ ((¬ (c0_mode ≠ c1_mode)) ∧ (c0_group < c1_group))) ↔ (shared_expr_Classification043_28 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_4872 c0_mode c1_mode) (normalization_4873 c0_mode c1_mode)) (and_congr (not_congr (normalization_4872 c0_mode c1_mode)) (normalization_4874 c0_group c1_group)))

abbrev shared_expr_Classification043_29 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∧ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification043_28 c0_group c0_mode c1_group c1_mode)))
theorem normalization_4876 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (((c0_level ≠ c1_level) ∧ (c0_level < c1_level)) ∨ ((¬ (c0_level ≠ c1_level)) ∧ (((c0_mode ≠ c1_mode) ∧ (c0_mode < c1_mode)) ∨ ((¬ (c0_mode ≠ c1_mode)) ∧ (c0_group < c1_group))))) ↔ (shared_expr_Classification043_29 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4870 c0_level c1_level) (normalization_4871 c0_level c1_level)) (and_congr (not_congr (normalization_4870 c0_level c1_level)) (normalization_4875 c0_group c0_mode c1_group c1_mode)))

abbrev shared_expr_Classification043_30 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Classification043_29 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_4877 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1449 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Classification043_30 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4869 c0_mode c1_mode) (normalization_3411 c0_mode)) (and_congr (not_congr (normalization_4869 c0_mode c1_mode)) (normalization_4876 c0_group c0_level c0_mode c1_group c1_level c1_mode)))

abbrev shared_expr_Classification043_31 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification043_30 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_4878 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (((c1_kind = (0 : Int)) ∧ (formula_1449 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ (c1_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Classification043_31 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (or_congr (and_congr (normalization_1317 c1_kind) (normalization_4877 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_1317 c1_kind)) (normalization_145)))

theorem normalization_4879 (c1_kind : Int) : (True ∧ (c1_kind = (1 : Int))) ↔ (True ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) := (and_congr (normalization_145) (normalization_1323 c1_kind))

theorem normalization_4880 (c0_depth c1_depth : Int) : (c0_depth = c1_depth) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_4881 (c0_node c1_node : Int) : (c0_node = c1_node) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_4882 (c0_sign c1_sign : Int) : ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int))) ↔ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) := (and_congr (normalization_3217 c0_sign) (normalization_1331 c1_sign))

theorem normalization_4883 (c0_node c1_node : Int) : (c0_node < c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Classification043_32 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ∧ ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))))
abbrev shared_expr_Classification043_33 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_32 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))
theorem normalization_4884 (c0_node c0_sign c1_node c1_sign : Int) : (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (c0_node < c1_node))) ↔ (shared_expr_Classification043_33 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_4881 c0_node c1_node) (normalization_4882 c0_sign c1_sign)) (and_congr (not_congr (normalization_4881 c0_node c1_node)) (normalization_4883 c0_node c1_node)))

theorem normalization_4885 (c0_depth c1_depth : Int) : ((c0_depth + (1 : Int)) = c1_depth) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_4886 (c0_node c1_node : Int) : (c0_node = (c1_node / (2 : Int))) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_4887 (c0_node c1_node : Int) : (c0_node < (c1_node / (2 : Int))) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Classification043_34 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)))) ∧ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))))
abbrev shared_expr_Classification043_35 (c0_node c0_sign c1_node : Int) : Prop := ((((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_34 c0_node c1_node))
theorem normalization_4888 (c0_node c0_sign c1_node : Int) : (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (c0_node < (c1_node / (2 : Int))))) ↔ (shared_expr_Classification043_35 c0_node c0_sign c1_node) := (or_congr (and_congr (normalization_4886 c0_node c1_node) (normalization_3217 c0_sign)) (and_congr (not_congr (normalization_4886 c0_node c1_node)) (normalization_4887 c0_node c1_node)))

theorem normalization_4889 (c0_depth c1_depth : Int) : ((c1_depth + (1 : Int)) = c0_depth) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_4890 (c0_node c1_node : Int) : (c1_node = (c0_node / (2 : Int))) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_4891 (c0_node c1_node : Int) : ((c0_node / (2 : Int)) < c1_node) ↔ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Classification043_36 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
abbrev shared_expr_Classification043_37 (c0_node c1_node c1_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification043_36 c0_node c1_node))
theorem normalization_4892 (c0_node c1_node c1_sign : Int) : (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ ((c0_node / (2 : Int)) < c1_node))) ↔ (shared_expr_Classification043_37 c0_node c1_node c1_sign) := (or_congr (and_congr (normalization_4890 c0_node c1_node) (normalization_1331 c1_sign)) (and_congr (not_congr (normalization_4890 c0_node c1_node)) (normalization_4891 c0_node c1_node)))

abbrev shared_expr_Classification043_38 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ∧ (shared_expr_Classification043_37 c0_node c1_node c1_sign)) ∨ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_4893 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : (formula_1450 c0_depth c0_node c1_depth c1_node c1_sign) ↔ (shared_expr_Classification043_38 c0_depth c0_node c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_4889 c0_depth c1_depth) (normalization_4892 c0_node c1_node c1_sign)) (and_congr (not_congr (normalization_4889 c0_depth c1_depth)) (normalization_145)))

abbrev shared_expr_Classification043_39 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification043_35 c0_node c0_sign c1_node)) ∨ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Classification043_38 c0_depth c0_node c1_depth c1_node c1_sign)))
theorem normalization_4894 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1451 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification043_39 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_4885 c0_depth c1_depth) (normalization_4888 c0_node c0_sign c1_node)) (and_congr (not_congr (normalization_4885 c0_depth c1_depth)) (normalization_4893 c0_depth c0_node c1_depth c1_node c1_sign)))

abbrev shared_expr_Classification043_40 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_39 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
abbrev shared_expr_Classification043_41 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification043_33 c0_node c0_sign c1_node c1_sign)) ∨ (shared_expr_Classification043_40 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
theorem normalization_4895 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1452 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification043_41 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_4880 c0_depth c1_depth) (normalization_4884 c0_node c0_sign c1_node c1_sign)) (and_congr (not_congr (normalization_4880 c0_depth c1_depth)) (normalization_4894 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

abbrev shared_expr_Classification043_42 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ∧ False) ∨ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification043_41 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
theorem normalization_4896 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c1_kind = (2 : Int)) ∧ False) ∨ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1452 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))) ↔ (shared_expr_Classification043_42 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_1322 c1_kind) (normalization_147)) (and_congr (not_congr (normalization_1322 c1_kind)) (normalization_4895 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

abbrev shared_expr_Classification043_43 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (True ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))))) ∨ ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification043_42 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_4897 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1453 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ (shared_expr_Classification043_43 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_3214 c0_kind) (normalization_4879 c1_kind)) (and_congr (not_congr (normalization_3214 c0_kind)) (normalization_4896 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Classification043_44 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_43 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_4898 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c1_kind = (0 : Int)) ∧ False) ∨ ((¬ (c1_kind = (0 : Int))) ∧ (formula_1453 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))) ↔ (shared_expr_Classification043_44 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_1317 c1_kind) (normalization_147)) (and_congr (not_congr (normalization_1317 c1_kind)) (normalization_4897 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Classification043_45 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Classification043_31 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ∨ ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_44 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
theorem normalization_4899 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1454 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (or_congr (and_congr (normalization_3209 c0_kind) (normalization_4878 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (and_congr (not_congr (normalization_3209 c0_kind)) (normalization_4898 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

theorem normalization_4900 (c1_kind : Int) : (¬ (c1_kind = (0 : Int))) ↔ (¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) := (not_congr (normalization_1317 c1_kind))

theorem normalization_4901 (c0_mode c1_mode : Int) : ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ↔ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) := (iff_congr (normalization_3411 c0_mode) (normalization_1824 c1_mode))

theorem normalization_4902 (c0_level c1_level : Int) : (c0_level = c1_level) ↔ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_4903 (c0_mode c1_mode : Int) : (c0_mode = c1_mode) ↔ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_4904 (c0_group c1_group : Int) : (c1_group ≤ c0_group) ↔ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4905 (c0_group c1_group : Int) : (¬ (c1_group ≤ c0_group)) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_4904 c0_group c1_group))

theorem normalization_4906 (c0_mode c1_mode : Int) : (c1_mode ≤ c0_mode) ↔ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4907 (c0_mode c1_mode : Int) : (¬ (c1_mode ≤ c0_mode)) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_4906 c0_mode c1_mode))

abbrev shared_expr_Classification043_46 (c0_group c0_mode c1_group c1_mode : Int) : Prop := (((((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))))
theorem normalization_4908 (c0_group c0_mode c1_group c1_mode : Int) : (((c0_mode = c1_mode) ∧ (¬ (c1_group ≤ c0_group))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ (c1_mode ≤ c0_mode)))) ↔ (shared_expr_Classification043_46 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_4903 c0_mode c1_mode) (normalization_4905 c0_group c1_group)) (and_congr (not_congr (normalization_4903 c0_mode c1_mode)) (normalization_4907 c0_mode c1_mode)))

theorem normalization_4909 (c0_level c1_level : Int) : (c1_level ≤ c0_level) ↔ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4910 (c0_level c1_level : Int) : (¬ (c1_level ≤ c0_level)) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4909 c0_level c1_level))

abbrev shared_expr_Classification043_47 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification043_46 c0_group c0_mode c1_group c1_mode)) ∨ ((¬ (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))))
theorem normalization_4911 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (((c0_level = c1_level) ∧ (((c0_mode = c1_mode) ∧ (¬ (c1_group ≤ c0_group))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ (c1_mode ≤ c0_mode))))) ∨ ((¬ (c0_level = c1_level)) ∧ (¬ (c1_level ≤ c0_level)))) ↔ (shared_expr_Classification043_47 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4902 c0_level c1_level) (normalization_4908 c0_group c0_mode c1_group c1_mode)) (and_congr (not_congr (normalization_4902 c0_level c1_level)) (normalization_4910 c0_level c1_level)))

abbrev shared_expr_Classification043_48 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification043_47 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_4912 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1455 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4901 c0_mode c1_mode) (normalization_4911 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_4901 c0_mode c1_mode)) (normalization_3411 c0_mode)))

theorem normalization_4913 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((¬ (c1_kind = (0 : Int))) ∨ (formula_1455 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_4900 c1_kind) (normalization_4912 c0_group c0_level c0_mode c1_group c1_level c1_mode))

theorem normalization_4914 (c1_kind : Int) : (¬ (c1_kind = (2 : Int))) ↔ (¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) := (not_congr (normalization_1322 c1_kind))

theorem normalization_4915 (c0_node c1_node : Int) : (c1_node ≤ c0_node) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4916 (c0_node c1_node : Int) : (¬ (c1_node ≤ c0_node)) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4915 c0_node c1_node))

abbrev shared_expr_Classification043_49 (c0_node c0_sign c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_32 c0_node c0_sign c1_node c1_sign) ∨ ((¬ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))))))
theorem normalization_4917 (c0_node c0_sign c1_node c1_sign : Int) : (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ (c1_node ≤ c0_node)))) ↔ (shared_expr_Classification043_49 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_4881 c0_node c1_node) (normalization_4882 c0_sign c1_sign)) (and_congr (not_congr (normalization_4881 c0_node c1_node)) (normalization_4916 c0_node c1_node)))

theorem normalization_4918 (c0_depth c1_depth : Int) : (c0_depth = ((-1 : Int) + c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_4919 (c0_node c1_node : Int) : ((c1_node / (2 : Int)) ≤ c0_node) ↔ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4920 (c0_node c1_node : Int) : (¬ ((c1_node / (2 : Int)) ≤ c0_node)) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (not_congr (normalization_4919 c0_node c1_node))

theorem normalization_4921 (c0_node c0_sign c1_node : Int) : (((c0_node = (c1_node / (2 : Int))) ∧ (c0_sign = (0 : Int))) ∨ ((¬ (c0_node = (c1_node / (2 : Int)))) ∧ (¬ ((c1_node / (2 : Int)) ≤ c0_node)))) ↔ (shared_expr_Classification043_35 c0_node c0_sign c1_node) := (or_congr (and_congr (normalization_4886 c0_node c1_node) (normalization_3217 c0_sign)) (and_congr (not_congr (normalization_4886 c0_node c1_node)) (normalization_4920 c0_node c1_node)))

theorem normalization_4922 (c0_depth c1_depth : Int) : (c1_depth = ((-1 : Int) + c0_depth)) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_4923 (c0_depth c1_depth : Int) : (¬ (c1_depth = ((-1 : Int) + c0_depth))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) := (not_congr (normalization_4922 c0_depth c1_depth))

theorem normalization_4924 (c0_node c1_node : Int) : (c1_node ≤ (c0_node / (2 : Int))) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4925 (c0_node c1_node : Int) : (¬ (c1_node ≤ (c0_node / (2 : Int)))) ↔ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4924 c0_node c1_node))

abbrev shared_expr_Classification043_50 (c0_node c1_node : Int) : Prop := ((¬ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Classification043_51 (c0_node c1_node c1_sign : Int) : Prop := ((((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ∨ (shared_expr_Classification043_50 c0_node c1_node))
theorem normalization_4926 (c0_node c1_node c1_sign : Int) : (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ (¬ (c1_node ≤ (c0_node / (2 : Int)))))) ↔ (shared_expr_Classification043_51 c0_node c1_node c1_sign) := (or_congr (and_congr (normalization_4890 c0_node c1_node) (normalization_1331 c1_sign)) (and_congr (not_congr (normalization_4890 c0_node c1_node)) (normalization_4925 c0_node c1_node)))

theorem normalization_4927 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : ((¬ (c1_depth = ((-1 : Int) + c0_depth))) ∨ (((c1_node = (c0_node / (2 : Int))) ∧ (c1_sign = (1 : Int))) ∨ ((¬ (c1_node = (c0_node / (2 : Int)))) ∧ (¬ (c1_node ≤ (c0_node / (2 : Int))))))) ↔ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Classification043_51 c0_node c1_node c1_sign)) := (or_congr (normalization_4923 c0_depth c1_depth) (normalization_4926 c0_node c1_node c1_sign))

abbrev shared_expr_Classification043_52 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Classification043_51 c0_node c1_node c1_sign)))
abbrev shared_expr_Classification043_53 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification043_35 c0_node c0_sign c1_node)) ∨ (shared_expr_Classification043_52 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_4928 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1456 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification043_53 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_4918 c0_depth c1_depth) (normalization_4921 c0_node c0_sign c1_node)) (and_congr (not_congr (normalization_4918 c0_depth c1_depth)) (normalization_4927 c0_depth c0_node c1_depth c1_node c1_sign)))

abbrev shared_expr_Classification043_54 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_53 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
abbrev shared_expr_Classification043_55 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification043_49 c0_node c0_sign c1_node c1_sign)) ∨ (shared_expr_Classification043_54 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
theorem normalization_4929 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1457 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification043_55 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_4880 c0_depth c1_depth) (normalization_4917 c0_node c0_sign c1_node c1_sign)) (and_congr (not_congr (normalization_4880 c0_depth c1_depth)) (normalization_4928 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

theorem normalization_4930 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : ((¬ (c1_kind = (2 : Int))) ∧ (formula_1457 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification043_55 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (and_congr (normalization_4914 c1_kind) (normalization_4929 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

abbrev shared_expr_Classification043_56 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification043_55 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev shared_expr_Classification043_57 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) ∨ (shared_expr_Classification043_56 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_4931 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1457 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) ↔ (shared_expr_Classification043_57 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_3214 c0_kind) (normalization_1323 c1_kind)) (and_congr (not_congr (normalization_3214 c0_kind)) (normalization_4930 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

theorem normalization_4932 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1458 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_57 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) := (and_congr (normalization_4900 c1_kind) (normalization_4931 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

abbrev shared_expr_Classification043_58 (c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
abbrev shared_expr_Classification043_59 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_57 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
abbrev shared_expr_Classification043_60 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_58 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Classification043_59 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_4933 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_60 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (or_congr (and_congr (normalization_3209 c0_kind) (normalization_4913 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (and_congr (not_congr (normalization_3209 c0_kind)) (normalization_4932 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Classification043_61 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_45 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_60 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
theorem normalization_4934 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1460 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_61 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (iff_congr (normalization_4899 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (normalization_4933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2341 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1460 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  classical
  have ht := (normalized_1193 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((c0_mode) ≤ (3 : Int)) ((c1_mode) ≤ (3 : Int)) (((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) (((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ((((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))) ∧ (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int))))) ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) (shared_expr_Classification043_35 c0_node c0_sign c1_node) ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int))) ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) (((c1_sign) ≤ (1 : Int)) ∧ (¬ ((c1_sign) ≤ (0 : Int)))) (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4934 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) hn

-- Checked replay of mp.
theorem replay_2342 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) (i174 : (formula_1454 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact Iff.mp (replay_2341 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) i174

abbrev shared_expr_Classification043_62 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
abbrev formula_1461 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_62 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem normalized_1194 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification043_63 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_60 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_60 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
theorem normalization_4935 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1461 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_63 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (iff_congr (normalization_4933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (normalization_4933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2343 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1461 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  classical
  have ht := (normalized_1194 (shared_expr_Classification043_60 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
  have hn := ht
  exact Iff.mpr (normalization_4935 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) hn

-- Checked replay of mp.
theorem replay_2344 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) (i174 : (formula_1454 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact Iff.mp (replay_2343 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (replay_2342 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign i174)

abbrev shared_expr_Classification043_64 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (((c0_level = c1_level) ∧ (((c0_mode = c1_mode) ∧ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))))) ∨ ((¬ (c0_level = c1_level)) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))))
abbrev formula_1462 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (shared_expr_Classification043_64 c0_group c0_level c0_mode c1_group c1_level c1_mode)

abbrev shared_expr_Classification043_65 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_1462 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))
abbrev formula_1463 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((¬ (c1_kind = (0 : Int))) ∨ (shared_expr_Classification043_65 c0_group c0_level c0_mode c1_group c1_level c1_mode))

abbrev shared_expr_Classification043_66 (c0_node c0_sign c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ∧ (c0_sign = (0 : Int))) ∨ ((¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_1464 (c0_node c0_sign c1_node : Int) : Prop := (shared_expr_Classification043_66 c0_node c0_sign c1_node)

abbrev shared_expr_Classification043_67 (c0_node c1_node c1_sign : Int) : Prop := ((((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ∧ (c1_sign = (1 : Int))) ∨ ((¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_1465 (c0_node c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_67 c0_node c1_node c1_sign)

abbrev shared_expr_Classification043_68 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ∧ (formula_1464 c0_node c0_sign c1_node)) ∨ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int))) ∧ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ∨ (formula_1465 c0_node c1_node c1_sign))))
abbrev formula_1466 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_68 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_69 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((c0_depth = c1_depth) ∧ (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)))))) ∨ ((¬ (c0_depth = c1_depth)) ∧ (formula_1466 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev formula_1467 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_69 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)

abbrev shared_expr_Classification043_70 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (c1_kind = (0 : Int))) ∧ (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))))
abbrev formula_1468 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_70 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)

abbrev shared_expr_Classification043_71 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (((c0_kind = (0 : Int)) ∧ (formula_1463 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ∨ ((¬ (c0_kind = (0 : Int))) ∧ (formula_1468 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
abbrev formula_1469 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_71 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

abbrev shared_expr_Classification043_72 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (formula_1469 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
abbrev formula_1470 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := (shared_expr_Classification043_72 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)

theorem normalized_1195 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ ((¬ p10) ∧ p11)) ∨ p12))))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ (p11 ∧ (¬ p10))) ∨ p12)))))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4936 (c0_group c1_group : Int) : ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)) ↔ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4937 (c0_group c1_group : Int) : (¬ ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)))) := (not_congr (normalization_4936 c0_group c1_group))

theorem normalization_4938 (c0_mode c1_mode : Int) : ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) ↔ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4939 (c0_mode c1_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_4938 c0_mode c1_mode))

theorem normalization_4940 (c0_group c0_mode c1_group c1_mode : Int) : (((c0_mode = c1_mode) ∧ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))) ∨ ((¬ (c0_mode = c1_mode)) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Classification043_46 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_4903 c0_mode c1_mode) (normalization_4937 c0_group c1_group)) (and_congr (not_congr (normalization_4903 c0_mode c1_mode)) (normalization_4939 c0_mode c1_mode)))

theorem normalization_4941 (c0_level c1_level : Int) : ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ↔ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4942 (c0_level c1_level : Int) : (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_4941 c0_level c1_level))

theorem normalization_4943 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1462 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Classification043_47 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4902 c0_level c1_level) (normalization_4940 c0_group c0_mode c1_group c1_mode)) (and_congr (not_congr (normalization_4902 c0_level c1_level)) (normalization_4942 c0_level c1_level)))

theorem normalization_4944 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (shared_expr_Classification043_65 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4901 c0_mode c1_mode) (normalization_4943 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_4901 c0_mode c1_mode)) (normalization_3411 c0_mode)))

theorem normalization_4945 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1463 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_4900 c1_kind) (normalization_4944 c0_group c0_level c0_mode c1_group c1_level c1_mode))

theorem normalization_4946 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int)) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4947 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4946 c0_node c1_node))

theorem normalization_4948 (c0_node c0_sign c1_node c1_sign : Int) : (((c0_node = c1_node) ∧ ((c0_sign = (0 : Int)) ∧ (c1_sign = (1 : Int)))) ∨ ((¬ (c0_node = c1_node)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≥ (0 : Int))))) ↔ (shared_expr_Classification043_49 c0_node c0_sign c1_node c1_sign) := (or_congr (and_congr (normalization_4881 c0_node c1_node) (normalization_4882 c0_sign c1_sign)) (and_congr (not_congr (normalization_4881 c0_node c1_node)) (normalization_4947 c0_node c1_node)))

theorem normalization_4949 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) = (-1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_4950 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (-1 : Int))) ∧ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_4951 (c0_node c1_node : Int) : ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_4952 (c0_node c1_node : Int) : (¬ ((c0_node + ((-1 : Int) * (c1_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c1_node / (2 : Int)) + ((-1 : Int) * c0_node)) ≤ (0 : Int))) := (not_congr (normalization_4951 c0_node c1_node))

theorem normalization_4953 (c0_node c0_sign c1_node : Int) : (formula_1464 c0_node c0_sign c1_node) ↔ (shared_expr_Classification043_35 c0_node c0_sign c1_node) := (or_congr (and_congr (normalization_4950 c0_node c1_node) (normalization_3217 c0_sign)) (and_congr (not_congr (normalization_4950 c0_node c1_node)) (normalization_4952 c0_node c1_node)))

theorem normalization_4954 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_4955 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ↔ (¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) := (not_congr (normalization_4954 c0_depth c1_depth))

theorem normalization_4956 (c0_node c1_node : Int) : ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) ∧ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_4957 (c0_node c1_node : Int) : ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4958 (c0_node c1_node : Int) : (¬ ((c1_node + ((-1 : Int) * (c0_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c0_node / (2 : Int)) + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (not_congr (normalization_4957 c0_node c1_node))

theorem normalization_4959 (c0_node c1_node c1_sign : Int) : (formula_1465 c0_node c1_node c1_sign) ↔ (shared_expr_Classification043_51 c0_node c1_node c1_sign) := (or_congr (and_congr (normalization_4956 c0_node c1_node) (normalization_1331 c1_sign)) (and_congr (not_congr (normalization_4956 c0_node c1_node)) (normalization_4958 c0_node c1_node)))

theorem normalization_4960 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) = (1 : Int))) ∨ (formula_1465 c0_node c1_node c1_sign)) ↔ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification043_51 c0_node c1_node c1_sign)) := (or_congr (normalization_4955 c0_depth c1_depth) (normalization_4959 c0_node c1_node c1_sign))

abbrev shared_expr_Classification043_73 (c0_depth c0_node c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Classification043_51 c0_node c1_node c1_sign)))
abbrev shared_expr_Classification043_74 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Classification043_35 c0_node c0_sign c1_node)) ∨ (shared_expr_Classification043_73 c0_depth c0_node c1_depth c1_node c1_sign))
theorem normalization_4961 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1466 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification043_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_4949 c0_depth c1_depth) (normalization_4953 c0_node c0_sign c1_node)) (and_congr (not_congr (normalization_4949 c0_depth c1_depth)) (normalization_4960 c0_depth c0_node c1_depth c1_node c1_sign)))

abbrev shared_expr_Classification043_75 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := ((¬ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_74 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
abbrev shared_expr_Classification043_76 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : Prop := (((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Classification043_49 c0_node c0_sign c1_node c1_sign)) ∨ (shared_expr_Classification043_75 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))
theorem normalization_4962 (c0_depth c0_node c0_sign c1_depth c1_node c1_sign : Int) : (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) ↔ (shared_expr_Classification043_76 c0_depth c0_node c0_sign c1_depth c1_node c1_sign) := (or_congr (and_congr (normalization_4880 c0_depth c1_depth) (normalization_4948 c0_node c0_sign c1_node c1_sign)) (and_congr (not_congr (normalization_4880 c0_depth c1_depth)) (normalization_4961 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))

theorem normalization_4963 (c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : ((¬ (c1_kind = (2 : Int))) ∧ (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification043_76 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)) := (and_congr (normalization_4914 c1_kind) (normalization_4962 c0_depth c0_node c0_sign c1_depth c1_node c1_sign))

abbrev shared_expr_Classification043_77 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ∧ (shared_expr_Classification043_76 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))
abbrev shared_expr_Classification043_78 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := (((((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) ∧ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) ∨ (shared_expr_Classification043_77 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_4964 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (((c0_kind = (2 : Int)) ∧ (c1_kind = (1 : Int))) ∨ ((¬ (c0_kind = (2 : Int))) ∧ ((¬ (c1_kind = (2 : Int))) ∧ (formula_1467 c0_depth c0_node c0_sign c1_depth c1_node c1_sign)))) ↔ (shared_expr_Classification043_78 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) := (or_congr (and_congr (normalization_3214 c0_kind) (normalization_1323 c1_kind)) (and_congr (not_congr (normalization_3214 c0_kind)) (normalization_4963 c0_depth c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

theorem normalization_4965 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : (formula_1468 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_78 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)) := (and_congr (normalization_4900 c1_kind) (normalization_4964 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))

abbrev shared_expr_Classification043_79 (c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign : Int) : Prop := ((¬ (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Classification043_78 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))
abbrev shared_expr_Classification043_80 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_58 c0_group c0_kind c0_level c0_mode c1_group c1_kind c1_level c1_mode) ∨ (shared_expr_Classification043_79 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign))
theorem normalization_4966 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1469 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_80 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (or_congr (and_congr (normalization_3209 c0_kind) (normalization_4945 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) (and_congr (not_congr (normalization_3209 c0_kind)) (normalization_4965 c0_depth c0_kind c0_node c0_sign c1_depth c1_kind c1_node c1_sign)))

abbrev shared_expr_Classification043_81 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : Prop := ((shared_expr_Classification043_60 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_80 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))
theorem normalization_4967 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1470 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ↔ (shared_expr_Classification043_81 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := (iff_congr (normalization_4933 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (normalization_4966 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign))

-- Checked replay of rewrite.
theorem replay_2345 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : (formula_1470 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  classical
  have ht := (normalized_1195 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) (((c0_kind) ≤ (2 : Int)) ∧ (¬ ((c0_kind) ≤ (1 : Int)))) (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (shared_expr_Classification043_49 c0_node c0_sign c1_node c1_sign) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-2 : Int)))) (shared_expr_Classification043_35 c0_node c0_sign c1_node) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) (shared_expr_Classification043_51 c0_node c1_node c1_sign))
  have hn := ht
  exact Iff.mpr (normalization_4967 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) hn

-- Checked replay of mp.
theorem replay_2346 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) (i174 : (formula_1454 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) : (formula_1469 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact Iff.mp (replay_2345 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (replay_2344 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign i174)

theorem normalized_1196 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4968 (c1_kind : Int) : (¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := (not_congr (normalization_1523 c1_kind))

theorem normalization_4969 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))))) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))))) := (iff_congr (normalization_4900 c1_kind) (normalization_4968 c1_kind))

-- Checked replay of monotonicity.
theorem replay_2347 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_1196 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))
  have n0 : ((((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_1525 c1_kind) (replay_591 c1_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_4969 c1_kind) hn

theorem normalized_1197 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4970 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ↔ ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_4968 c1_kind) (normalization_1522 c1_kind))

-- Checked replay of rewrite.
theorem replay_2348 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1197 ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_4970 c1_kind) hn

theorem normalized_1198 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4971 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) ↔ ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_4900 c1_kind) (normalization_1522 c1_kind))

-- Checked replay of trans.
theorem replay_2349 (c1_kind : Int) : ((¬ (c1_kind = (0 : Int))) ↔ ((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_1198 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))
  have n0 : ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))))) := by
    exact Iff.mp (normalization_4969 c1_kind) (replay_2347 c1_kind)
  have n1 : ((¬ (¬ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_4970 c1_kind) (replay_2348 c1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4971 c1_kind) hn

abbrev shared_expr_Classification043_82 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((shared_expr_Classification043_65 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_764 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1471 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (shared_expr_Classification043_82 c0_group c0_level c0_mode c1_group c1_level c1_mode)

theorem normalized_1199 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4972 (c0_level c1_level : Int) : ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ↔ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_4973 (c0_level c1_level : Int) : (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ↔ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) := (not_congr (normalization_4972 c0_level c1_level))

theorem normalization_4974 (c0_level c1_level : Int) : ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ↔ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) := (or_congr (normalization_4973 c0_level c1_level) (normalization_4942 c0_level c1_level))

theorem normalization_4975 (c0_mode c1_mode : Int) : ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ↔ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_4976 (c0_mode c1_mode : Int) : (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ↔ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) := (not_congr (normalization_4975 c0_mode c1_mode))

theorem normalization_4977 (c0_mode c1_mode : Int) : ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_4976 c0_mode c1_mode) (normalization_4939 c0_mode c1_mode))

abbrev shared_expr_Classification043_83 (c0_group c0_mode c1_group c1_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int))))))
theorem normalization_4978 (c0_group c0_mode c1_group c1_mode : Int) : (formula_763 c0_group c0_mode c1_group c1_mode) ↔ (shared_expr_Classification043_83 c0_group c0_mode c1_group c1_mode) := (or_congr (and_congr (normalization_4977 c0_mode c1_mode) (normalization_4939 c0_mode c1_mode)) (and_congr (not_congr (normalization_4977 c0_mode c1_mode)) (normalization_4937 c0_group c1_group)))

abbrev shared_expr_Classification043_84 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Classification043_83 c0_group c0_mode c1_group c1_mode)))
theorem normalization_4979 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_764 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Classification043_84 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4974 c0_level c1_level) (normalization_4942 c0_level c1_level)) (and_congr (not_congr (normalization_4974 c0_level c1_level)) (normalization_4978 c0_group c0_mode c1_group c1_mode)))

abbrev shared_expr_Classification043_85 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) ∧ (shared_expr_Classification043_84 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int))))) ∧ (¬ ((c0_mode) ≤ (3 : Int)))))
theorem normalization_4980 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_764 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))) ↔ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode) := (or_congr (and_congr (normalization_4901 c0_mode c1_mode) (normalization_4979 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (and_congr (not_congr (normalization_4901 c0_mode c1_mode)) (normalization_3411 c0_mode)))

theorem normalization_4981 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1471 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ ((shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (iff_congr (normalization_4944 c0_group c0_level c0_mode c1_group c1_level c1_mode) (normalization_4980 c0_group c0_level c0_mode c1_group c1_level c1_mode))

-- Checked replay of rewrite.
theorem replay_2350 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_1471 c0_group c0_level c0_mode c1_group c1_level c1_mode) := by
  classical
  have ht := (normalized_1199 ((¬ ((c0_mode) ≤ (3 : Int))) ↔ (¬ ((c1_mode) ≤ (3 : Int)))) ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (-1 : Int)) ((c0_group + ((-1 : Int) * c1_group)) ≤ (-1 : Int)) ((c0_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4981 c0_group c0_level c0_mode c1_group c1_level c1_mode) hn

abbrev shared_expr_Classification043_86 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((¬ (c1_kind ≤ (0 : Int))) ∨ (¬ (c1_kind ≥ (0 : Int)))) ∨ ((((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int))) ∧ (formula_764 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c1_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int)))))
abbrev formula_1472 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (shared_expr_Classification043_86 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)

theorem normalized_1200 (p0 p1 p2 p3 : Prop) : ((((¬ p0) ↔ p1) ∧ (p2 ↔ p3)) → (((¬ p0) ∨ p2) ↔ (p1 ∨ p3))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4982 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1472 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_1522 c1_kind) (normalization_4980 c0_group c0_level c0_mode c1_group c1_level c1_mode))

abbrev shared_expr_Classification043_87 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ (((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_4983 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1463 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1472 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ↔ (shared_expr_Classification043_87 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (iff_congr (normalization_4945 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (normalization_4982 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode))

-- Checked replay of monotonicity.
theorem replay_2351 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1463 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1472 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) := by
  classical
  have ht := (normalized_1200 (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int)))) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode) (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode))
  have n0 : ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_4971 c1_kind) (replay_2349 c1_kind)
  have n1 : ((shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode) ↔ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := by
    exact Iff.mp (normalization_4981 c0_group c0_level c0_mode c1_group c1_level c1_mode) (replay_2350 c0_group c0_level c0_mode c1_group c1_level c1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4983 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) hn

theorem normalized_1201 (p0 p1 p2 : Prop) : ((((¬ p0) ∨ (¬ (¬ p1))) ∨ p2) ↔ ((¬ p0) ∨ (¬ (¬ p1)) ∨ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4984 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)) := (or_congr (normalization_1520 c1_kind) (or_congr (normalization_1521 c1_kind) (normalization_4980 c0_group c0_level c0_mode c1_group c1_level c1_mode)))

abbrev shared_expr_Classification043_88 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := ((((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_4985 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1472 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ↔ (shared_expr_Classification043_88 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (iff_congr (normalization_4982 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (normalization_4984 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode))

-- Checked replay of rewrite.
theorem replay_2352 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1472 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) := by
  classical
  have ht := (normalized_1201 ((c1_kind) ≤ (0 : Int)) ((c1_kind) ≤ (-1 : Int)) (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode))
  have hn := ht
  exact Iff.mpr (normalization_4985 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) hn

theorem normalized_1202 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Classification043_89 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : Prop := (((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ↔ ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
theorem normalization_4986 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1463 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) ↔ (shared_expr_Classification043_89 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := (iff_congr (normalization_4945 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (normalization_4984 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode))

-- Checked replay of trans.
theorem replay_2353 (c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode : Int) : ((formula_1463 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) ↔ (formula_1439 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)) := by
  classical
  have ht := (normalized_1202 ((¬ (((c1_kind) ≤ (0 : Int)) ∧ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_48 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ((¬ ((c1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (-1 : Int)))) ∨ (shared_expr_Classification043_85 c0_group c0_level c0_mode c1_group c1_level c1_mode)))
  have n0 : (shared_expr_Classification043_87 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := by
    exact Iff.mp (normalization_4983 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (replay_2351 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)
  have n1 : (shared_expr_Classification043_88 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) := by
    exact Iff.mp (normalization_4985 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) (replay_2352 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4986 c0_group c0_level c0_mode c1_group c1_kind c1_level c1_mode) hn

theorem normalized_1203 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4987 (c1_kind : Int) : ((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int))) ↔ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) := (and_congr (normalization_1587 c1_kind) (normalization_1589 c1_kind))

theorem normalization_4988 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ ((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int)))) ↔ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) := (iff_congr (normalization_1323 c1_kind) (normalization_4987 c1_kind))

-- Checked replay of rewrite.
theorem replay_2354 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ ((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int)))) := by
  classical
  have ht := (normalized_1203 (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_4988 c1_kind) hn

theorem normalized_1204 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4989 (c1_kind : Int) : ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))) ↔ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))) := (or_congr (normalization_1588 c1_kind) (normalization_1590 c1_kind))

theorem normalization_4990 (c1_kind : Int) : (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int))))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int)))))) := (not_congr (normalization_4989 c1_kind))

theorem normalization_4991 (c1_kind : Int) : (((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) ↔ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_4987 c1_kind) (normalization_4990 c1_kind))

-- Checked replay of rewrite.
theorem replay_2355 (c1_kind : Int) : (((c1_kind ≤ (1 : Int)) ∧ (c1_kind ≥ (1 : Int))) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1204 ((c1_kind) ≤ (1 : Int)) ((c1_kind) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_4991 c1_kind) hn

theorem normalized_1205 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4992 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) ↔ ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := (iff_congr (normalization_1323 c1_kind) (normalization_4990 c1_kind))

-- Checked replay of trans.
theorem replay_2356 (c1_kind : Int) : ((c1_kind = (1 : Int)) ↔ (¬ ((¬ (c1_kind ≤ (1 : Int))) ∨ (¬ (c1_kind ≥ (1 : Int)))))) := by
  classical
  have ht := (normalized_1205 (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))))
  have n0 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int))))) := by
    exact Iff.mp (normalization_4988 c1_kind) (replay_2354 c1_kind)
  have n1 : ((((c1_kind) ≤ (1 : Int)) ∧ (¬ ((c1_kind) ≤ (0 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (0 : Int))))))) := by
    exact Iff.mp (normalization_4991 c1_kind) (replay_2355 c1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4992 c1_kind) hn

theorem normalized_1206 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4993 (c1_kind : Int) : (¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := (not_congr (normalization_1616 c1_kind))

theorem normalization_4994 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))))) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) := (iff_congr (normalization_4914 c1_kind) (normalization_4993 c1_kind))

-- Checked replay of monotonicity.
theorem replay_2357 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ (¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))))) := by
  classical
  have ht := (normalized_1206 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))
  have n0 : ((((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ↔ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) := by
    exact Iff.mp (normalization_1677 c1_kind) (replay_626 c1_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_4994 c1_kind) hn

theorem normalized_1207 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4995 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ↔ ((¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_4993 c1_kind) (normalization_1615 c1_kind))

-- Checked replay of rewrite.
theorem replay_2358 (c1_kind : Int) : ((¬ (¬ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int)))))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_1207 ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_4995 c1_kind) hn

theorem normalized_1208 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4996 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) ↔ ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := (iff_congr (normalization_4914 c1_kind) (normalization_1615 c1_kind))

-- Checked replay of trans.
theorem replay_2359 (c1_kind : Int) : ((¬ (c1_kind = (2 : Int))) ↔ ((¬ (c1_kind ≤ (2 : Int))) ∨ (¬ (c1_kind ≥ (2 : Int))))) := by
  classical
  have ht := (normalized_1208 (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int)))) ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))
  have n0 : ((¬ (((c1_kind) ≤ (2 : Int)) ∧ (¬ ((c1_kind) ≤ (1 : Int))))) ↔ (¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))))) := by
    exact Iff.mp (normalization_4994 c1_kind) (replay_2357 c1_kind)
  have n1 : ((¬ (¬ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int))))))) ↔ ((¬ ((c1_kind) ≤ (2 : Int))) ∨ (¬ (¬ ((c1_kind) ≤ (1 : Int)))))) := by
    exact Iff.mp (normalization_4995 c1_kind) (replay_2358 c1_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_4996 c1_kind) hn

theorem normalized_1209 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_4997 (c0_depth c1_depth : Int) : (c0_depth ≤ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_4998 (c0_depth c1_depth : Int) : (c0_depth ≥ c1_depth) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_4999 (c0_depth c1_depth : Int) : ((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_4997 c0_depth c1_depth) (normalization_4998 c0_depth c1_depth))

abbrev shared_expr_Classification043_90 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))
theorem normalization_5000 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ ((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth))) ↔ (shared_expr_Classification043_90 c0_depth c1_depth) := (iff_congr (normalization_4880 c0_depth c1_depth) (normalization_4999 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2360 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ ((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth))) := by
  classical
  have ht := (normalized_1209 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5000 c0_depth c1_depth) hn

theorem normalized_1210 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5001 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_5002 (c0_depth c1_depth : Int) : ((c0_depth ≤ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := (iff_congr (normalization_4997 c0_depth c1_depth) (normalization_5001 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2361 (c0_depth c1_depth : Int) : ((c0_depth ≤ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := by
  classical
  have ht := (normalized_1210 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5002 c0_depth c1_depth) hn

theorem normalized_1211 (p0 : Prop) : ((¬ p0) ↔ (¬ p0)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5003 (c0_depth c1_depth : Int) : ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5004 (c0_depth c1_depth : Int) : ((c0_depth ≥ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (iff_congr (normalization_4998 c0_depth c1_depth) (normalization_5003 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2362 (c0_depth c1_depth : Int) : ((c0_depth ≥ c1_depth) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) := by
  classical
  have ht := (normalized_1211 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5004 c0_depth c1_depth) hn

theorem normalized_1212 (p0 p1 p2 : Prop) : (((p0 ↔ p0) ∧ ((¬ p1) ↔ (¬ p1))) → (p2 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5005 (c0_depth c1_depth : Int) : (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (and_congr (normalization_5001 c0_depth c1_depth) (normalization_5003 c0_depth c1_depth))

theorem normalization_5006 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ↔ (shared_expr_Classification043_90 c0_depth c1_depth) := (iff_congr (normalization_4999 c0_depth c1_depth) (normalization_5005 c0_depth c1_depth))

-- Checked replay of monotonicity.
theorem replay_2363 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1212 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)) (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))
  have n0 : (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ↔ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := by
    exact Iff.mp (normalization_5002 c0_depth c1_depth) (replay_2361 c0_depth c1_depth)
  have n1 : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := by
    exact Iff.mp (normalization_5004 c0_depth c1_depth) (replay_2362 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5006 c0_depth c1_depth) hn

abbrev shared_expr_Classification043_91 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))))
abbrev formula_1473 (c0_depth c1_depth : Int) : Prop := (shared_expr_Classification043_91 c0_depth c1_depth)

theorem normalized_1213 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5007 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ↔ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) := (not_congr (normalization_5001 c0_depth c1_depth))

theorem normalization_5008 (c0_depth c1_depth : Int) : (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_5003 c0_depth c1_depth))

theorem normalization_5009 (c0_depth c1_depth : Int) : ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))) ↔ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_5007 c0_depth c1_depth) (normalization_5008 c0_depth c1_depth))

theorem normalization_5010 (c0_depth c1_depth : Int) : (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))) := (not_congr (normalization_5009 c0_depth c1_depth))

abbrev shared_expr_Classification043_92 (c0_depth c1_depth : Int) : Prop := ((((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))))))
theorem normalization_5011 (c0_depth c1_depth : Int) : (formula_1473 c0_depth c1_depth) ↔ (shared_expr_Classification043_92 c0_depth c1_depth) := (iff_congr (normalization_5005 c0_depth c1_depth) (normalization_5010 c0_depth c1_depth))

-- Checked replay of rewrite.
theorem replay_2364 (c0_depth c1_depth : Int) : (formula_1473 c0_depth c1_depth) := by
  classical
  have ht := (normalized_1213 ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_5011 c0_depth c1_depth) hn

theorem normalized_1214 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5012 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification043_92 c0_depth c1_depth) := (iff_congr (normalization_4999 c0_depth c1_depth) (normalization_5010 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2365 (c0_depth c1_depth : Int) : (((c0_depth ≤ c1_depth) ∧ (c0_depth ≥ c1_depth)) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1214 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (shared_expr_Classification043_92 c0_depth c1_depth))
  have n0 : (shared_expr_Classification043_90 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5006 c0_depth c1_depth) (replay_2363 c0_depth c1_depth)
  have n1 : (shared_expr_Classification043_92 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5011 c0_depth c1_depth) (replay_2364 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5012 c0_depth c1_depth) hn

theorem normalized_1215 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5013 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) ↔ (shared_expr_Classification043_92 c0_depth c1_depth) := (iff_congr (normalization_4880 c0_depth c1_depth) (normalization_5010 c0_depth c1_depth))

-- Checked replay of trans.
theorem replay_2366 (c0_depth c1_depth : Int) : ((c0_depth = c1_depth) ↔ (¬ ((¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1215 (((c0_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ∧ (¬ ((c0_depth + ((-1 : Int) * c1_depth)) ≤ (-1 : Int)))) (shared_expr_Classification043_92 c0_depth c1_depth))
  have n0 : (shared_expr_Classification043_90 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5000 c0_depth c1_depth) (replay_2360 c0_depth c1_depth)
  have n1 : (shared_expr_Classification043_92 c0_depth c1_depth) := by
    exact Iff.mp (normalization_5012 c0_depth c1_depth) (replay_2365 c0_depth c1_depth)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_5013 c0_depth c1_depth) hn

theorem normalized_1216 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_5014 (c0_node c1_node : Int) : (c0_node ≤ c1_node) ↔ ((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_5015 (c0_node c1_node : Int) : (c0_node ≥ c1_node) ↔ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_5016 (c0_node c1_node : Int) : ((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node)) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) := (and_congr (normalization_5014 c0_node c1_node) (normalization_5015 c0_node c1_node))

abbrev shared_expr_Classification043_93 (c0_node c1_node : Int) : Prop := ((((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))) ↔ (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
theorem normalization_5017 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ ((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node))) ↔ (shared_expr_Classification043_93 c0_node c1_node) := (iff_congr (normalization_4881 c0_node c1_node) (normalization_5016 c0_node c1_node))

-- Checked replay of rewrite.
theorem replay_2367 (c0_node c1_node : Int) : ((c0_node = c1_node) ↔ ((c0_node ≤ c1_node) ∧ (c0_node ≥ c1_node))) := by
  classical
  have ht := (normalized_1216 (((c0_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)) ∧ (¬ ((c0_node + ((-1 : Int) * c1_node)) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_5017 c0_node c1_node) hn

end H4Formal.Generated.Classification
