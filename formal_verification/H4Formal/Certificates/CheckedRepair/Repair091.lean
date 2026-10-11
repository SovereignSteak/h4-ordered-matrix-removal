import H4Formal.Certificates.CheckedRepair.Repair090

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem propositional_1961 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5987 (c2_node c2_sign r3_node r3_sign : Int) : ((formula_8 c2_node c2_sign r3_node r3_sign) ∨ (c2_sign ≤ (0 : Int))) := by
  exact (propositional_1961 (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((c2_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_5988 (c2_node c2_sign h r2_depth r2_node r2_sign r3_node r3_sign : Int) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : (formula_8 c2_node c2_sign r3_node r3_sign) := by
  exact (Or.elim (replay_5987 c2_node c2_sign r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim ((replay_5969 c2_node c2_sign h r2_depth r2_node r2_sign i363) t0))))

-- Checked replay of unit-resolution.
theorem replay_5989 (c2_node c2_sign h r2_depth r2_node r2_sign r3_node r3_sign : Int) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : (¬ ((¬ (formula_8 c2_node c2_sign r3_node r3_sign)) ∨ (¬ (formula_9 c2_node c2_sign r3_node r3_sign)))) := by
  exact (Or.elim (replay_5983 c2_node c2_sign r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_5988 c2_node c2_sign h r2_depth r2_node r2_sign r3_node r3_sign i363)))) (fun t1 => (False.elim (t1 (replay_5986 c2_node c2_sign h r2_depth r2_node r2_sign r3_node r3_sign i363)))))))

-- Checked replay of unit-resolution.
theorem replay_5990 (c2_depth c2_node c2_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : (formula_10 c2_depth c2_node c2_sign r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_5982 c2_depth c2_node c2_sign r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_5989 c2_node c2_sign h r2_depth r2_node r2_sign r3_node r3_sign i363) t0))))

-- Checked replay of unit-resolution.
theorem replay_5991 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i1 : (formula_25 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i200 : (formula_1557 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i177 : (formula_1226 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i183 : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i339 : ((formula_2139 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ False)) (i27 : ((formula_407 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) (i210 : ((formula_1654 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) (i163 : ((formula_1060 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ False)) (i9 : ((formula_100 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i271 : ((formula_1975 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ False)) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i176 : ((formula_1164 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ False)) (i223 : ((formula_1816 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) (i178 : ((formula_1289 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : (¬ ((¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int))) ∨ (¬ (formula_6 c2_node c2_sign h r3_depth r3_node r3_sign)))) := by
  exact (Or.elim (replay_3 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim (l0 (replay_5981 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i30 i146 i10 i93 i154 i181 i1 i33 i200 i62 i177 i23 i183 i157 i182 i339 i27 i210 i162 i163 i9 i271 i15 i176 i223 i178 i363)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_5990 c2_depth c2_node c2_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i363)))))))

-- Checked replay of unit-resolution.
theorem replay_5992 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i30 : (formula_505 h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign)) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i154 : (formula_782 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i1 : (formula_25 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h)) (i33 : (formula_531 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i200 : (formula_1557 r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i177 : (formula_1226 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i183 : (formula_1459 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign)) (i157 : (formula_805 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i182 : (formula_1390 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign)) (i339 : ((formula_2139 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ False)) (i27 : ((formula_407 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) (i210 : ((formula_1654 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign) ↔ True)) (i162 : ((formula_913 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ True)) (i163 : ((formula_1060 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ False)) (i9 : ((formula_100 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i271 : ((formula_1975 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ False)) (i15 : ((formula_232 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign) ↔ True)) (i176 : ((formula_1164 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ False)) (i223 : ((formula_1816 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) (i178 : ((formula_1289 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ True)) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : ((r3_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_2 c2_depth c2_node c2_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_5991 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign h r0_depth r0_group r0_kind r0_level r0_mode r0_node r0_sign r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i30 i146 i10 i93 i154 i181 i1 i33 i200 i62 i177 i23 i183 i157 i182 i339 i27 i210 i162 i163 i9 i271 i15 i176 i223 i178 i363) l0))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_5993 (c3_depth h r3_depth : Int) : (((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair091_0 (c3_node c3_sign r2_node r2_sign : Int) : Prop := ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2229 (c3_node c3_sign r2_node r2_sign : Int) : Prop := (shared_expr_Repair091_0 c3_node c3_sign r2_node r2_sign)

abbrev shared_expr_Repair091_1 (c3_node c3_sign r2_node r2_sign : Int) : Prop := (((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))))
abbrev formula_2230 (c3_node c3_sign r2_node r2_sign : Int) : Prop := (shared_expr_Repair091_1 c3_node c3_sign r2_node r2_sign)

theorem propositional_1962 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ (p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ p6)))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5994 (c3_node c3_sign r2_node r2_sign : Int) : (((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign))) ∨ (formula_2229 c3_node c3_sign r2_node r2_sign)) := by
  exact (propositional_1962 (formula_2229 c3_node c3_sign r2_node r2_sign) ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))

abbrev shared_expr_Repair091_2 (c3_node c3_sign r2_node r2_sign : Int) : Prop := ((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2231 (c3_node c3_sign r2_node r2_sign : Int) : Prop := (shared_expr_Repair091_2 c3_node c3_sign r2_node r2_sign)

theorem propositional_1963 (p0 p1 p2 p3 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> by_cases case_p2 : p2 <;> simp [case_p0, case_p1, case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5995 (c3_node c3_sign r2_node r2_sign : Int) : (formula_2231 c3_node c3_sign r2_node r2_sign) := by
  exact (propositional_1963 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Repair091_3 (c3_node r2_node r3_node : Int) : Prop := ((¬ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≥ (0 : Int))) ∨ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)) ∨ (¬ ((r2_node % (2 : Int)) ≥ (0 : Int))) ∨ (¬ ((r3_node % (2 : Int)) ≤ (1 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * (((2 : Int) * (r3_node / (2 : Int))) + (r3_node % (2 : Int))))) ≤ (0 : Int))) ∨ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)))
abbrev formula_2232 (c3_node r2_node r3_node : Int) : Prop := (shared_expr_Repair091_3 c3_node r2_node r3_node)

-- Checked replay of th-lemma.
theorem replay_5996 (c3_node r2_node r3_node : Int) : (formula_2232 c3_node r2_node r3_node) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair091_4 (c3_node c3_sign r3_node r3_sign : Int) : Prop := ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev formula_2233 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_4 c3_node c3_sign r3_node r3_sign)

theorem propositional_1964 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5997 (c3_node c3_sign r3_node r3_sign : Int) : ((formula_2233 c3_node c3_sign r3_node r3_sign) ∨ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int))) := by
  exact (propositional_1964 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))

abbrev shared_expr_Repair091_5 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))))
abbrev formula_2234 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_5 c3_node c3_sign r3_node r3_sign)

abbrev shared_expr_Repair091_6 (c3_node c3_sign r3_node r3_sign : Int) : Prop := ((¬ ((¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2234 c3_node c3_sign r3_node r3_sign)))) ∨ (¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2234 c3_node c3_sign r3_node r3_sign)))
abbrev formula_2235 (c3_node c3_sign r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_6 c3_node c3_sign r3_node r3_sign)

theorem propositional_1965 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5998 (c3_node c3_sign r3_node r3_sign : Int) : (formula_2235 c3_node c3_sign r3_node r3_sign) := by
  exact (propositional_1965 (formula_2233 c3_node c3_sign r3_node r3_sign) (formula_2234 c3_node c3_sign r3_node r3_sign))

abbrev shared_expr_Repair091_7 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ ((¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2234 c3_node c3_sign r3_node r3_sign)))))
abbrev formula_2236 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_7 c3_depth c3_node c3_sign r3_depth r3_node r3_sign)

theorem propositional_1966 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_5999 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : ((formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) ∨ ((¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2234 c3_node c3_sign r3_node r3_sign)))) := by
  exact (propositional_1966 ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2234 c3_node c3_sign r3_node r3_sign))))

abbrev shared_expr_Repair091_8 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ∨ (¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))) ∨ (¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev formula_2237 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_8 c3_node c3_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Repair091_9 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ∨ ((r3_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ∨ (¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))
abbrev formula_2238 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_9 c3_node c3_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Repair091_10 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)))
abbrev formula_2239 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_10 c3_node c3_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Repair091_11 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign)))) ∨ (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign)))
abbrev formula_2240 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_11 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)

abbrev shared_expr_Repair091_12 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign)))) ∨ (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign)))
abbrev formula_2241 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_12 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)

theorem propositional_1967 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6000 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : (formula_2241 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_1967 ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))) (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign))

abbrev shared_expr_Repair091_13 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))) ∨ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))
abbrev formula_2242 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_13 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)

theorem propositional_1968 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6001 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) : (formula_2242 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_1968 ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Repair091_14 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign)))
abbrev formula_2243 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_14 c3_node c3_sign h r3_depth r3_node r3_sign)

theorem propositional_1969 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6002 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : (formula_2243 c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_1969 ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign) (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign))

theorem propositional_1970 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)) ∨ p5) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6003 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : ((formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign) ∨ (c3_sign ≥ (2 : Int))) := by
  exact (propositional_1970 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_6004 (c3_sign : Int) : ((c3_sign ≥ (1 : Int)) ∨ (¬ (c3_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_6005 (c3_sign : Int) : ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1971 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ p6))) ∨ (¬ p7))) ∨ (¬ (p8 ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ ((¬ p11) ∨ (¬ p12))) ∨ (¬ p6)))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6006 (c3_depth c3_node c3_sign r3_depth r3_node r3_sign : Int) : ((formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) ∨ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := by
  exact (propositional_1971 ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))) ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)) ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_6007 (c3_sign : Int) : ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_1972 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6008 (c3_sign : Int) : (((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ∨ (c3_sign ≤ (1 : Int))) := by
  exact (propositional_1972 (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)))

abbrev shared_expr_Repair091_15 (c3_sign : Int) : Prop := ((¬ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_2244 (c3_sign : Int) : Prop := (shared_expr_Repair091_15 c3_sign)

theorem propositional_1973 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6009 (c3_sign : Int) : (formula_2244 c3_sign) := by
  exact (propositional_1973 ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))) ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))

theorem propositional_1974 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6010 (c3_sign : Int) : (((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))) ∨ (c3_sign ≤ (0 : Int))) := by
  exact (propositional_1974 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6011 (c3_sign : Int) (i365 : (¬ (c3_sign ≤ (0 : Int)))) : ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))) := by
  exact (Or.elim (replay_6010 c3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i365 t0))))

-- Checked replay of unit-resolution.
theorem replay_6012 (c3_sign : Int) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) : (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) := by
  exact (Or.elim (replay_6009 c3_sign) (fun l0 => (False.elim (l0 i366))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6011 c3_sign i365)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6013 (c3_sign : Int) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) : (c3_sign ≤ (1 : Int)) := by
  exact (Or.elim (replay_6008 c3_sign) (fun l0 => (False.elim ((replay_6012 c3_sign i365 i366) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6014 (c3_sign : Int) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) : (¬ (c3_sign ≥ (2 : Int))) := by
  exact (Or.elim (replay_6007 c3_sign) (fun l0 => (False.elim (l0 (replay_6013 c3_sign i365 i366)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6015 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_6003 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t105))))))))))))))))))) (fun t0 => (False.elim ((replay_6014 c3_sign i365 i366) t0))))

theorem propositional_1975 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ (¬ p0)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6016 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) : ((formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := by
  exact (propositional_1975 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6017 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) : (formula_2238 c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_6016 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t104)))))))))))))))) (fun t0 => (False.elim (t0 i364))))

-- Checked replay of unit-resolution.
theorem replay_6018 (c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) : (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign)) := by
  exact (Or.elim (replay_6002 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i367))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6015 c3_node c3_sign h r3_depth r3_node r3_sign i365 i366)))) (fun t2 => (False.elim (t2 (replay_6017 c3_node c3_sign h r3_depth r3_node r3_sign i364)))))))))

-- Checked replay of unit-resolution.
theorem replay_6019 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) : ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))) := by
  exact (Or.elim (replay_6001 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6018 c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367) t0))))

-- Checked replay of unit-resolution.
theorem replay_6020 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign)) := by
  exact (Or.elim (replay_6000 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim (l0 i368))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6019 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6021 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_6006 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_6020 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367 i368) l0))) (fun t0 => t0))

abbrev shared_expr_Repair091_16 (c3_depth c3_node c3_sign r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ ((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign)))))
abbrev formula_2245 (c3_depth c3_node c3_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair091_16 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)

abbrev shared_expr_Repair091_17 (c3_depth c3_node c3_sign r2_depth r2_node r2_sign : Int) : Prop := ((¬ (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ ((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign)))))
abbrev formula_2246 (c3_depth c3_node c3_sign r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair091_17 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)

theorem propositional_1976 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6022 (c3_depth c3_node c3_sign r2_depth r2_node r2_sign : Int) : (formula_2246 c3_depth c3_node c3_sign r2_depth r2_node r2_sign) := by
  exact (propositional_1976 ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign))))

theorem propositional_1977 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ p4))) ∨ (¬ p5))) ∨ (¬ p6)) ∨ p6) := by
  classical
  first | (by_cases case_p6 : p6 <;> simp [case_p6, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6023 (c3_node c3_sign r2_node r2_sign : Int) : (((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign))) ∨ (formula_2230 c3_node c3_sign r2_node r2_sign)) := by
  exact (propositional_1977 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))) ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) (formula_2230 c3_node c3_sign r2_node r2_sign))

abbrev shared_expr_Repair091_18 (c3_node c3_sign r2_node r2_sign : Int) : Prop := ((¬ (formula_2230 c3_node c3_sign r2_node r2_sign)) ∨ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))))
abbrev formula_2247 (c3_node c3_sign r2_node r2_sign : Int) : Prop := (shared_expr_Repair091_18 c3_node c3_sign r2_node r2_sign)

theorem propositional_1978 (p0 p1 p2 p3 : Prop) : ((¬ (p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3))) ∨ p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> by_cases case_p2 : p2 <;> simp [case_p0, case_p1, case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6024 (c3_node c3_sign r2_node r2_sign : Int) : (formula_2247 c3_node c3_sign r2_node r2_sign) := by
  exact (propositional_1978 ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))))

abbrev shared_expr_Repair091_19 (c3_node r2_node r3_node : Int) : Prop := ((¬ ((r3_node + ((-1 : Int) * (((2 : Int) * (r3_node / (2 : Int))) + (r3_node % (2 : Int))))) ≤ (0 : Int))) ∨ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ ((r3_node % (2 : Int)) ≤ (1 : Int))) ∨ (¬ ((r2_node % (2 : Int)) ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≥ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))))
abbrev formula_2248 (c3_node r2_node r3_node : Int) : Prop := (shared_expr_Repair091_19 c3_node r2_node r3_node)

-- Checked replay of th-lemma.
theorem replay_6025 (c3_node r2_node r3_node : Int) : (formula_2248 c3_node r2_node r3_node) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_6026 (r3_node : Int) : ((¬ (r3_node = (((2 : Int) * (r3_node / (2 : Int))) + (r3_node % (2 : Int))))) ∨ ((r3_node + ((-1 : Int) * (((2 : Int) * (r3_node / (2 : Int))) + (r3_node % (2 : Int))))) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_6027 (r3_node : Int) : (False ∨ (r3_node = (((2 : Int) * (r3_node / (2 : Int))) + (r3_node % (2 : Int))))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of true-axiom.
theorem replay_6028  : True := by
  exact True.intro

-- Checked replay of unit-resolution.
theorem replay_6029 (r3_node : Int) : (r3_node = (((2 : Int) * (r3_node / (2 : Int))) + (r3_node % (2 : Int)))) := by
  exact (Or.elim (replay_6027 r3_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6030 (r3_node : Int) : ((r3_node + ((-1 : Int) * (((2 : Int) * (r3_node / (2 : Int))) + (r3_node % (2 : Int))))) ≤ (0 : Int)) := by
  exact (Or.elim (replay_6026 r3_node) (fun l0 => (False.elim (l0 (replay_6029 r3_node)))) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_6031 (r3_node : Int) : (False ∨ ((r3_node % (2 : Int)) ≤ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6032 (r3_node : Int) : ((r3_node % (2 : Int)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_6031 r3_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_6033 (r2_node : Int) : (False ∨ ((r2_node % (2 : Int)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6034 (r2_node : Int) : ((r2_node % (2 : Int)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_6033 r2_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

-- Checked replay of th-lemma.
theorem replay_6035 (r2_node : Int) : ((¬ (r2_node = (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ∨ ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_6036 (r2_node : Int) : (False ∨ (r2_node = (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6037 (r2_node : Int) : (r2_node = (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int)))) := by
  exact (Or.elim (replay_6036 r2_node) (fun l0 => (False.elim l0)) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6038 (r2_node : Int) : ((r2_node + ((-1 : Int) * (((2 : Int) * (r2_node / (2 : Int))) + (r2_node % (2 : Int))))) ≥ (0 : Int)) := by
  exact (Or.elim (replay_6035 r2_node) (fun l0 => (False.elim (l0 (replay_6037 r2_node)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6039 (c3_node r2_node r3_node : Int) : (((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) ∨ (¬ ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int)))) := by
  exact (Or.elim (replay_6025 c3_node r2_node r3_node) (fun l0 => (False.elim (l0 (replay_6030 r3_node)))) (fun t0 => (Or.elim t0 (fun l1 => (Or.inl l1)) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6032 r3_node)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6034 r2_node)))) (fun t3 => (Or.elim t3 (fun l4 => (Or.inr (Or.inl l4))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_6038 r2_node)))) (fun t5 => (Or.inr (Or.inr t5))))))))))))))

theorem propositional_1979 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6040 (c3_node c3_sign r3_node r3_sign : Int) : ((formula_2234 c3_node c3_sign r3_node r3_sign) ∨ (¬ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)))) := by
  exact (propositional_1979 ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6041 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2234 c3_node c3_sign r3_node r3_sign))) := by
  exact (Or.elim (replay_5999 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_6020 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367 i368) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

theorem propositional_1980 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6042 (c3_node c3_sign r3_node r3_sign : Int) : ((formula_2233 c3_node c3_sign r3_node r3_sign) ∨ (c3_sign ≤ (0 : Int))) := by
  exact (propositional_1980 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6043 (c3_node c3_sign r3_node r3_sign : Int) (i365 : (¬ (c3_sign ≤ (0 : Int)))) : (formula_2233 c3_node c3_sign r3_node r3_sign) := by
  exact (Or.elim (replay_6042 c3_node c3_sign r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim (i365 t0))))

-- Checked replay of unit-resolution.
theorem replay_6044 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (formula_2234 c3_node c3_sign r3_node r3_sign)) := by
  exact (Or.elim (replay_5998 c3_node c3_sign r3_node r3_sign) (fun l0 => (False.elim (l0 (replay_6041 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367 i368)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6043 c3_node c3_sign r3_node r3_sign i365)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6045 (c3_depth c3_node c3_sign h r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int))) := by
  exact (Or.elim (replay_6040 c3_node c3_sign r3_node r3_sign) (fun l0 => (False.elim ((replay_6044 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367 i368) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6046 (c3_depth c3_node c3_sign h r2_node r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i369 : ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≤ (0 : Int))) := by
  exact (Or.elim (replay_6039 c3_node r2_node r3_node) (fun l0 => (False.elim ((replay_6045 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367 i368) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i369))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_6047 (c3_sign : Int) : ((c3_sign ≤ (0 : Int)) ∨ (c3_sign ≥ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6048 (c3_sign : Int) (i365 : (¬ (c3_sign ≤ (0 : Int)))) : (c3_sign ≥ (1 : Int)) := by
  exact (Or.elim (replay_6047 c3_sign) (fun l0 => (False.elim (i365 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6049 (c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i369 : ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (formula_2230 c3_node c3_sign r2_node r2_sign)) := by
  exact (Or.elim (replay_6024 c3_node c3_sign r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_6046 c3_depth c3_node c3_sign h r2_node r3_depth r3_node r3_sign i364 i365 i366 i369 i367 i368) l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6013 c3_sign i365 i366)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6048 c3_sign i365)))) (fun t3 => (False.elim (t3 i65))))))))))

-- Checked replay of unit-resolution.
theorem replay_6050 (c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i369 : ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign))) := by
  exact (Or.elim (replay_6023 c3_node c3_sign r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_6049 c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign i364 i365 i366 i369 i65 i367 i368) t0))))

-- Checked replay of unit-resolution.
theorem replay_6051 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i369 : ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i370 : ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := by
  exact (Or.elim (replay_6022 c3_depth c3_node c3_sign r2_depth r2_node r2_sign) (fun l0 => (False.elim (l0 i371))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i370))) (fun t2 => (False.elim (t2 (replay_6050 c3_depth c3_node c3_sign h r2_node r2_sign r3_depth r3_node r3_sign i364 i365 i366 i369 i65 i367 i368)))))))))

-- Checked replay of th-lemma.
theorem replay_6052 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i365 : (¬ (c3_sign ≤ (0 : Int)))) (i366 : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))) (i369 : ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i370 : ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : False := by
  classical
  have k0 := i364
  have k1 := (replay_6021 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign i364 i365 i366 i367 i368)
  have k2 := (replay_6051 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i364 i365 i366 i369 i65 i370 i371 i367 i368)
  have k3 := i372
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair091_20 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : Prop := ((c3_sign ≤ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (¬ (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) ∨ (¬ (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))))
abbrev formula_2249 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair091_20 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_6053 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : (formula_2249 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6052 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))

-- Checked replay of th-lemma.
theorem replay_6054 (c3_depth h r2_depth : Int) : (((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6055 (c3_depth h r2_depth : Int) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) := by
  exact (Or.elim (replay_6054 c3_depth h r2_depth) (fun l0 => (False.elim (i373 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i69))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_6056 (r2_node r3_node : Int) : (((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)) ∨ ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6057 (r2_node r3_node : Int) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) : ((r2_node + ((-1 : Int) * r3_node)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_6056 r2_node r3_node) (fun l0 => (False.elim (i374 l0))) (fun t0 => t0))

abbrev shared_expr_Repair091_21 (c3_depth c3_sign h : Int) : Prop := (((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ∧ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))))
abbrev shared_expr_Repair091_22 (c3_depth c3_sign h : Int) : Prop := ((shared_expr_Repair091_21 c3_depth c3_sign h) ∨ ((¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))))
abbrev formula_2250 (c3_depth c3_sign h : Int) : Prop := (shared_expr_Repair091_22 c3_depth c3_sign h)

abbrev shared_expr_Repair091_23 (c3_depth c3_sign h : Int) : Prop := ((¬ (formula_2250 c3_depth c3_sign h)) ∨ (¬ ((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))))
abbrev formula_2251 (c3_depth c3_sign h : Int) : Prop := (shared_expr_Repair091_23 c3_depth c3_sign h)

theorem propositional_1981 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6058 (c3_depth c3_sign h : Int) : (formula_2251 c3_depth c3_sign h) := by
  exact (propositional_1981 ((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)))

theorem propositional_1982 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6059 (c3_depth h : Int) : (((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) ∨ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) := by
  exact (propositional_1982 ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6060 (c3_depth h : Int) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) : ((¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := by
  exact (Or.elim (replay_6059 c3_depth h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i373 t0))))

-- Checked replay of unit-resolution.
theorem replay_6061 (c3_depth c3_sign h : Int) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) : ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))))) := by
  exact (Or.elim (replay_6058 c3_depth c3_sign h) (fun l0 => (False.elim (l0 i375))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6060 c3_depth h i373)))) (fun t1 => (Or.elim t1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))))

-- Checked replay of unit-resolution.
theorem replay_6062 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (c3_sign ≤ (0 : Int)) := by
  exact (Or.elim (replay_6053 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i364))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i372))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6055 c3_depth h r2_depth i69 i373)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i371))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i65))) (fun t5 => (Or.elim t5 (fun l6 => (False.elim (l6 (replay_6057 r2_node r3_node i374)))) (fun t6 => (Or.elim t6 (fun l7 => (False.elim (l7 i368))) (fun t7 => (Or.elim t7 (fun l8 => (False.elim (l8 i367))) (fun t8 => (False.elim (t8 (replay_6061 c3_depth c3_sign h i373 i375)))))))))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_6063 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (c3_sign ≥ (1 : Int))) := by
  exact (Or.elim (replay_6005 c3_sign) (fun l0 => (False.elim (l0 (replay_6062 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6064 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (c3_sign ≥ (2 : Int))) := by
  exact (Or.elim (replay_6004 c3_sign) (fun l0 => (False.elim ((replay_6063 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6065 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (formula_2237 c3_node c3_sign h r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_6003 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t105))))))))))))))))))) (fun t0 => (False.elim ((replay_6064 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) t0))))

-- Checked replay of unit-resolution.
theorem replay_6066 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign)) := by
  exact (Or.elim (replay_6002 c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i367))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6065 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t2 => (False.elim (t2 (replay_6017 c3_node c3_sign h r3_depth r3_node r3_sign i364)))))))))

-- Checked replay of unit-resolution.
theorem replay_6067 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2239 c3_node c3_sign h r3_depth r3_node r3_sign))) := by
  exact (Or.elim (replay_6001 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6066 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) t0))))

-- Checked replay of unit-resolution.
theorem replay_6068 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (formula_2236 c3_depth c3_node c3_sign r3_depth r3_node r3_sign)) := by
  exact (Or.elim (replay_6000 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim (l0 i368))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6067 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6069 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) ∨ (¬ (formula_2234 c3_node c3_sign r3_node r3_sign))) := by
  exact (Or.elim (replay_5999 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_6068 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

theorem propositional_1983 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((¬ p5) ∨ (¬ p6)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6070 (c3_node c3_sign r3_node r3_sign : Int) : ((formula_2234 c3_node c3_sign r3_node r3_sign) ∨ (c3_sign ≥ (1 : Int))) := by
  exact (propositional_1983 ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6071 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (formula_2234 c3_node c3_sign r3_node r3_sign) := by
  exact (Or.elim (replay_6070 c3_node c3_sign r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim ((replay_6063 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) t0))))

-- Checked replay of unit-resolution.
theorem replay_6072 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (formula_2233 c3_node c3_sign r3_node r3_sign)) := by
  exact (Or.elim (replay_5998 c3_node c3_sign r3_node r3_sign) (fun l0 => (False.elim (l0 (replay_6069 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_6071 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))))))

-- Checked replay of unit-resolution.
theorem replay_6073 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((c3_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)) := by
  exact (Or.elim (replay_5997 c3_node c3_sign r3_node r3_sign) (fun l0 => (False.elim ((replay_6072 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6074 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((c3_node + ((-1 : Int) * (r2_node / (2 : Int)))) ≥ (0 : Int)) := by
  exact (Or.elim (replay_5996 c3_node r2_node r3_node) (fun l0 => (False.elim (l0 (replay_6038 r2_node)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i374 l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6034 r2_node)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6032 r3_node)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_6073 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_6030 r3_node)))) (fun t5 => t5))))))))))))

theorem propositional_1984 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6075 (c3_sign : Int) : (((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int)))) ∨ (c3_sign ≥ (0 : Int))) := by
  exact (propositional_1984 (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)))

end H4Formal.Generated.Repair
