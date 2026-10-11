import H4Formal.Certificates.CheckedRepair.Repair099

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem propositional_2199 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6453 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h : Int) : ((formula_1361 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) ∨ (c1_sign ≥ (0 : Int))) := by
  exact (propositional_2199 (c1_mode ≥ (6 : Int)) (c1_mode ≥ (0 : Int)) (c1_depth ≤ (0 : Int)) (c1_depth ≥ (0 : Int)) (c1_node ≤ (0 : Int)) (c1_node ≥ (0 : Int)) (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)) (c1_kind ≤ (0 : Int)) (c1_kind ≥ (0 : Int)) (c1_level ≥ (1 : Int)) ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int)) (c1_group ≤ (1 : Int)) (c1_group ≥ (1 : Int)) (c1_group ≤ (2 : Int)) (c1_group ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6454 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h : Int) (i388 : (¬ (c1_sign ≥ (0 : Int)))) : (formula_1361 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) := by
  exact (Or.elim (replay_6453 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i388 t0))))

theorem propositional_2200 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p13) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6455 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) : ((formula_1372 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) ∨ (c1_sign ≥ (0 : Int))) := by
  exact (propositional_2200 (c1_kind ≤ (2 : Int)) (c1_kind ≥ (2 : Int)) (c1_mode ≤ (0 : Int)) (c1_mode ≥ (0 : Int)) (c1_level ≤ (0 : Int)) (c1_level ≥ (0 : Int)) (c1_group ≤ (0 : Int)) (c1_group ≥ (0 : Int)) (c1_depth ≤ (0 : Int)) (c1_depth ≥ (0 : Int)) (c1_node ≤ (0 : Int)) (c1_node ≥ (0 : Int)) (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6456 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign : Int) (i388 : (¬ (c1_sign ≥ (0 : Int)))) : (formula_1372 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) := by
  exact (Or.elim (replay_6455 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i388 t0))))

-- Checked replay of unit-resolution.
theorem replay_6457 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h : Int) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i388 : (¬ (c1_sign ≥ (0 : Int)))) : (¬ (formula_1374 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) := by
  exact (Or.elim (replay_2811 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h i181) (fun l0 => (False.elim (l0 (replay_6456 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign i388)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6454 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h i388)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6458 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h : Int) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i388 : (¬ (c1_sign ≥ (0 : Int)))) : (formula_1373 c1_depth c1_sign h) := by
  exact (Or.elim (replay_6452 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h) (fun l0 => (False.elim ((replay_6457 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h i181 i388) l0))) (fun t0 => t0))

abbrev shared_expr_Repair100_0 (c1_sign : Int) : Prop := ((¬ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))) ∨ (¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))
abbrev formula_2582 (c1_sign : Int) : Prop := (shared_expr_Repair100_0 c1_sign)

theorem propositional_2201 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6459 (c1_sign : Int) : (formula_2582 c1_sign) := by
  exact (propositional_2201 ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))) ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))

theorem propositional_2202 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6460 (c1_sign : Int) : (((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))) ∨ (c1_sign ≥ (0 : Int))) := by
  exact (propositional_2202 (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6461 (c1_sign : Int) (i388 : (¬ (c1_sign ≥ (0 : Int)))) : ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int)))) := by
  exact (Or.elim (replay_6460 c1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i388 t0))))

-- Checked replay of unit-resolution.
theorem replay_6462 (c1_sign : Int) (i388 : (¬ (c1_sign ≥ (0 : Int)))) (i389 : ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) : (¬ ((¬ ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))))) := by
  exact (Or.elim (replay_6459 c1_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6461 c1_sign i388)))) (fun t1 => (False.elim (t1 i389))))))

-- Checked replay of unit-resolution.
theorem replay_6463 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h : Int) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) (i388 : (¬ (c1_sign ≥ (0 : Int)))) (i390 : ((¬ ((h + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) (i389 : ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int))))) : False := by
  exact (Or.elim (replay_6451 c1_depth c1_sign h) (fun l0 => (False.elim (l0 (replay_6458 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h i181 i388)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i390))) (fun t1 => (False.elim ((replay_6462 c1_sign i388 i389) t1))))))

-- Checked replay of lemma.
theorem replay_6464 (c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h : Int) (i181 : (formula_1366 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h)) : ((c1_sign ≥ (0 : Int)) ∨ (¬ ((¬ ((h + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c1_depth)) ≤ (0 : Int))))) ∨ (¬ ((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6463 c1_depth c1_group c1_kind c1_level c1_mode c1_node c1_sign h i181 (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr q)))))

theorem propositional_2203 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6465 (c1_sign : Int) : (((¬ (c1_sign ≤ (1 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))) ∨ (c1_sign ≥ (1 : Int))) := by
  exact (propositional_2203 (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_6466 (c1_sign : Int) : ((¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair100_1 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (formula_1772 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign)))) ∨ (¬ (formula_1771 c1_depth c1_node c1_sign r3_depth r3_node r3_sign)))
abbrev formula_2583 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair100_1 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)

theorem propositional_2204 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6467 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_2583 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_2204 ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign))) (formula_1771 c1_depth c1_node c1_sign r3_depth r3_node r3_sign))

theorem propositional_2205 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6468 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) : ((formula_1771 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) ∨ ((¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign)))) := by
  exact (propositional_2205 ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (1 : Int)) ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (1 : Int)) ((¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign))))

abbrev shared_expr_Repair100_2 (c1_node c1_sign r3_node r3_sign : Int) : Prop := ((¬ ((¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign)))) ∨ (¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign)))
abbrev formula_2584 (c1_node c1_sign r3_node r3_sign : Int) : Prop := (shared_expr_Repair100_2 c1_node c1_sign r3_node r3_sign)

theorem propositional_2206 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6469 (c1_node c1_sign r3_node r3_sign : Int) : (formula_2584 c1_node c1_sign r3_node r3_sign) := by
  exact (propositional_2206 (formula_1769 c1_node c1_sign r3_node r3_sign) (formula_1770 c1_node c1_sign r3_node r3_sign))

theorem propositional_2207 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6470 (c1_node c1_sign r3_node r3_sign : Int) : ((formula_1769 c1_node c1_sign r3_node r3_sign) ∨ (c1_sign ≤ (0 : Int))) := by
  exact (propositional_2207 (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)) ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6471 (c1_node c1_sign r3_node r3_sign : Int) (i391 : (¬ (c1_sign ≤ (0 : Int)))) : (formula_1769 c1_node c1_sign r3_node r3_sign) := by
  exact (Or.elim (replay_6470 c1_node c1_sign r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.inr (Or.inr (Or.inr t102)))))))))) (fun t0 => (False.elim (i391 t0))))

-- Checked replay of unit-resolution.
theorem replay_6472 (c1_node c1_sign r3_node r3_sign : Int) (i391 : (¬ (c1_sign ≤ (0 : Int)))) (i392 : (formula_1770 c1_node c1_sign r3_node r3_sign)) : (¬ ((¬ (formula_1769 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign)))) := by
  exact (Or.elim (replay_6469 c1_node c1_sign r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6471 c1_node c1_sign r3_node r3_sign i391)))) (fun t1 => (False.elim (t1 i392))))))

-- Checked replay of unit-resolution.
theorem replay_6473 (c1_depth c1_node c1_sign r3_depth r3_node r3_sign : Int) (i391 : (¬ (c1_sign ≤ (0 : Int)))) (i392 : (formula_1770 c1_node c1_sign r3_node r3_sign)) : (formula_1771 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) := by
  exact (Or.elim (replay_6468 c1_depth c1_node c1_sign r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6472 c1_node c1_sign r3_node r3_sign i391 i392) t0))))

abbrev shared_expr_Repair100_3 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign))) ∨ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign))
abbrev formula_2585 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair100_3 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)

theorem propositional_2208 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6474 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_2585 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_2208 ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int)) (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign))

abbrev shared_expr_Repair100_4 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int))))) ∨ (¬ (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign)))
abbrev formula_2586 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair100_4 c1_node c1_sign h r3_depth r3_node r3_sign)

theorem propositional_2209 (p0 p1 p2 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2)) := by
  classical
  first | (by_cases case_p0 : p0 <;> by_cases case_p1 : p1 <;> simp [case_p0, case_p1, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6475 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_2586 c1_node c1_sign h r3_depth r3_node r3_sign) := by
  exact (propositional_2209 ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign) (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign))

theorem propositional_2210 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6476 (c1_node c1_sign r3_node r3_sign : Int) : (((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) ∨ (c1_sign ≤ (0 : Int))) := by
  exact (propositional_2210 (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (c1_sign ≤ (0 : Int)) (c1_sign ≥ (0 : Int)) ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6477 (c1_node c1_sign r3_node r3_sign : Int) (i391 : (¬ (c1_sign ≤ (0 : Int)))) : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c1_sign ≤ (0 : Int))) ∨ (¬ (c1_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c1_node)) ≤ (0 : Int)))) := by
  exact (Or.elim (replay_6476 c1_node c1_sign r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim (i391 t0))))

-- Checked replay of unit-resolution.
theorem replay_6478 (c1_node c1_sign h r3_depth r3_node r3_sign : Int) (i391 : (¬ (c1_sign ≤ (0 : Int)))) (i393 : (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign)) (i394 : (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign)) : (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign)) := by
  exact (Or.elim (replay_6475 c1_node c1_sign h r3_depth r3_node r3_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6477 c1_node c1_sign r3_node r3_sign i391)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i393))) (fun t2 => (False.elim (t2 i394))))))))

-- Checked replay of unit-resolution.
theorem replay_6479 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) (i391 : (¬ (c1_sign ≤ (0 : Int)))) (i393 : (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign)) (i394 : (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign)) : ((¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_1768 c1_node c1_sign h r3_depth r3_node r3_sign))) := by
  exact (Or.elim (replay_6474 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6478 c1_node c1_sign h r3_depth r3_node r3_sign i391 i393 i394) t0))))

-- Checked replay of unit-resolution.
theorem replay_6480 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) (i391 : (¬ (c1_sign ≤ (0 : Int)))) (i393 : (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign)) (i394 : (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign)) (i395 : (formula_1772 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)) (i392 : (formula_1770 c1_node c1_sign r3_node r3_sign)) : False := by
  exact (Or.elim (replay_6467 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) (fun l0 => (False.elim (l0 i395))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6479 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign i391 i393 i394)))) (fun t1 => (False.elim (t1 (replay_6473 c1_depth c1_node c1_sign r3_depth r3_node r3_sign i391 i392)))))))

abbrev shared_expr_Repair100_5 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := ((c1_sign ≤ (0 : Int)) ∨ (¬ (formula_1772 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_1770 c1_node c1_sign r3_node r3_sign)) ∨ (¬ (formula_1766 c1_node c1_sign h r3_depth r3_node r3_sign)) ∨ (¬ (formula_1767 c1_node c1_sign h r3_depth r3_node r3_sign)))
abbrev formula_2587 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair100_5 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_6481 (c1_depth c1_node c1_sign h r3_depth r3_node r3_sign : Int) : (formula_2587 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6480 c1_depth c1_node c1_sign h r3_depth r3_node r3_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))))

theorem propositional_2211 (p0 p1 p2 p3 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6482 (c1_node c1_sign r3_node r3_sign : Int) : ((formula_1770 c1_node c1_sign r3_node r3_sign) ∨ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) := by
  exact (propositional_2211 ((c1_node + ((-1 : Int) * (r3_node / (2 : Int)))) ≤ (0 : Int)) (c1_sign ≤ (1 : Int)) (c1_sign ≥ (1 : Int)) ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))))

theorem propositional_2212 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6483 (r3_sign : Int) : (((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))) ∨ (r3_sign ≥ (2 : Int))) := by
  exact (propositional_2212 (r3_sign ≤ (2 : Int)) (r3_sign ≥ (2 : Int)))

abbrev shared_expr_Repair100_6 (r3_sign : Int) : Prop := ((¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) ∨ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))
abbrev formula_2588 (r3_sign : Int) : Prop := (shared_expr_Repair100_6 r3_sign)

theorem propositional_2213 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6484 (r3_sign : Int) : (formula_2588 r3_sign) := by
  exact (propositional_2213 ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))

theorem propositional_2214 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6485 (r3_sign : Int) : (((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) ∨ (r3_sign ≥ (1 : Int))) := by
  exact (propositional_2214 (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6486 (r3_sign : Int) (i396 : (¬ (r3_sign ≥ (1 : Int)))) : ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))) := by
  exact (Or.elim (replay_6485 r3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim (i396 t0))))

-- Checked replay of unit-resolution.
theorem replay_6487 (r3_sign : Int) (i396 : (¬ (r3_sign ≥ (1 : Int)))) (i397 : ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) : (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_6484 r3_sign) (fun l0 => (False.elim (l0 i397))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6486 r3_sign i396)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_6488 (r3_sign : Int) (i396 : (¬ (r3_sign ≥ (1 : Int)))) : (¬ (r3_sign ≥ (2 : Int))) := by
  exact (Or.elim (replay_6356 r3_sign) (fun l0 => (False.elim (i396 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6489 (r3_sign : Int) (i396 : (¬ (r3_sign ≥ (1 : Int)))) (i397 : ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) : False := by
  exact (Or.elim (replay_6483 r3_sign) (fun l0 => (False.elim ((replay_6487 r3_sign i396 i397) l0))) (fun t0 => (False.elim ((replay_6488 r3_sign i396) t0))))

-- Checked replay of lemma.
theorem replay_6490 (r3_sign : Int) : ((r3_sign ≥ (1 : Int)) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6489 r3_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

theorem propositional_2215 (p0 p1 p2 p3 p4 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6491 (c2_node c2_sign r3_node r3_sign : Int) : (((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∨ (r3_sign ≤ (0 : Int))) := by
  exact (propositional_2215 (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((r3_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))

theorem propositional_2216 (p0 p1 p2 p3 p4 p5 : Prop) : ((p0 ∨ p1 ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) ∨ p5) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6492 (c2_node c2_sign h r3_depth r3_node r3_sign : Int) : ((formula_5 c2_node c2_sign h r3_depth r3_node r3_sign) ∨ (c2_sign ≥ (1 : Int))) := by
  exact (propositional_2216 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((r3_node + ((-1 : Int) * c2_node)) ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) (c2_sign ≤ (1 : Int)) (c2_sign ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_6493 (c0_depth c2_depth r1_level : Int) : (((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ∨ ((r1_level + ((-1 : Int) * c2_depth)) ≥ (1 : Int)) ∨ (¬ ((c0_depth + ((-1 : Int) * c2_depth)) ≥ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_6494 (c0_depth r1_level : Int) : ((¬ ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_2217 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3))) ∨ (¬ ((¬ p4) ∨ (¬ p5))))) ∨ (¬ p6) ∨ (¬ p7)) ∨ p7) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6495 (c0_depth c0_kind c0_sign r1_level : Int) : ((formula_879 c0_depth c0_kind c0_sign r1_level) ∨ ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int))) := by
  exact (propositional_2217 (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) (c0_sign ≤ (1 : Int)) (c0_sign ≥ (1 : Int)) (c0_sign ≤ (2 : Int)) (c0_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))

theorem propositional_2218 (p0 p1 p2 p3 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6496 (c0_depth c0_kind c0_sign r1_group r1_level : Int) : ((¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) ∨ (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ (formula_879 c0_depth c0_kind c0_sign r1_level))) := by
  exact (propositional_2218 ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) (formula_879 c0_depth c0_kind c0_sign r1_level) (c0_kind ≤ (2 : Int)) (c0_kind ≥ (2 : Int)))

theorem propositional_2219 (p0 p1 p2 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6497 (c0_depth c0_kind c0_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level))) ∨ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)) := by
  exact (propositional_2219 (r1_mode ≤ (1 : Int)) (r1_mode ≥ (1 : Int)) (formula_880 c0_depth c0_kind c0_sign r1_group r1_level))

abbrev shared_expr_Repair100_7 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) ∨ (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_2589 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair100_7 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

theorem propositional_2220 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6498 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_2589 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  exact (propositional_2220 ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level))) ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level))) ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level))))

theorem propositional_2221 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6499 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ∨ (r1_mode ≥ (3 : Int))) := by
  exact (propositional_2221 (r1_mode ≤ (3 : Int)) (r1_mode ≥ (3 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ((c0_node % (2 : Int)) ≥ (1 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))

-- Checked replay of th-lemma.
theorem replay_6500 (r1_mode : Int) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair100_8 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))
abbrev formula_2590 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := (shared_expr_Repair100_8 c3_depth c3_kind c3_sign r1_level)

abbrev shared_expr_Repair100_9 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := ((((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∧ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))))
abbrev formula_2591 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair100_9 c3_depth c3_kind c3_sign r1_group r1_level)

abbrev shared_expr_Repair100_10 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int))))
abbrev formula_2592 (c3_depth c3_kind c3_sign r1_level : Int) : Prop := (shared_expr_Repair100_10 c3_depth c3_kind c3_sign r1_level)

abbrev shared_expr_Repair100_11 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := ((((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∧ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))))
abbrev formula_2593 (c3_depth c3_kind c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair100_11 c3_depth c3_kind c3_sign r1_group r1_level)

abbrev shared_expr_Repair100_12 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))
abbrev formula_2594 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (shared_expr_Repair100_12 c3_depth c3_kind c3_node c3_sign r1_level)

abbrev shared_expr_Repair100_13 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∧ (¬ (formula_2594 c3_depth c3_kind c3_node c3_sign r1_level))) ∨ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))))
abbrev formula_2595 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair100_13 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair100_14 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))
abbrev formula_2596 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (shared_expr_Repair100_14 c3_depth c3_kind c3_node c3_sign r1_level)

abbrev shared_expr_Repair100_15 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∧ (¬ (formula_2596 c3_depth c3_kind c3_node c3_sign r1_level))) ∨ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_2590 c3_depth c3_kind c3_sign r1_level))))
abbrev formula_2597 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair100_15 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair100_16 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))
abbrev formula_2598 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (shared_expr_Repair100_16 c3_depth c3_kind c3_node c3_sign r1_level)

abbrev shared_expr_Repair100_17 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∧ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_2598 c3_depth c3_kind c3_node c3_sign r1_level))))
abbrev formula_2599 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair100_17 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair100_18 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))))))) ∨ (¬ ((c3_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))
abbrev formula_2600 (c3_depth c3_kind c3_node c3_sign r1_level : Int) : Prop := (shared_expr_Repair100_18 c3_depth c3_kind c3_node c3_sign r1_level)

abbrev shared_expr_Repair100_19 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := ((((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ∧ (¬ (formula_2592 c3_depth c3_kind c3_sign r1_level))) ∨ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∧ (¬ (formula_2600 c3_depth c3_kind c3_node c3_sign r1_level))))
abbrev formula_2601 (c3_depth c3_kind c3_node c3_sign r1_group r1_level : Int) : Prop := (shared_expr_Repair100_19 c3_depth c3_kind c3_node c3_sign r1_group r1_level)

abbrev shared_expr_Repair100_20 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
abbrev formula_2602 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair100_20 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

abbrev shared_expr_Repair100_21 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) ∨ (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
abbrev formula_2603 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair100_21 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

theorem propositional_2222 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6501 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2603 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
  exact (propositional_2222 ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level))) ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level))) ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level))))

theorem propositional_2223 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((¬ p8) ∨ (¬ p9))))) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p12) ∨ (¬ p13))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6502 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level))) ∨ (r1_mode ≤ (0 : Int))) := by
  exact (propositional_2223 (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_6503 (r1_mode : Int) : ((r1_mode ≥ (1 : Int)) ∨ (r1_mode ≤ (2 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6504 (r1_mode : Int) (i398 : (¬ (r1_mode ≤ (2 : Int)))) : (r1_mode ≥ (1 : Int)) := by
  exact (Or.elim (replay_6503 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (i398 t0))))

-- Checked replay of unit-resolution.
theorem replay_6505 (r1_mode : Int) (i398 : (¬ (r1_mode ≤ (2 : Int)))) : (¬ (r1_mode ≤ (0 : Int))) := by
  exact (Or.elim (replay_2092 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_6504 r1_mode i398)))))

-- Checked replay of unit-resolution.
theorem replay_6506 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) (i398 : (¬ (r1_mode ≤ (2 : Int)))) : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6502 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6505 r1_mode i398) t0))))

theorem propositional_2224 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((¬ p8) ∨ (¬ p9))))) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p12) ∨ (¬ p13))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6507 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level))) ∨ (r1_mode ≤ (1 : Int))) := by
  exact (propositional_2224 (r1_mode ≤ (1 : Int)) (r1_mode ≥ (1 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)))

-- Checked replay of th-lemma.
theorem replay_6508 (r1_mode : Int) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (r1_mode ≤ (2 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6509 (r1_mode : Int) (i398 : (¬ (r1_mode ≤ (2 : Int)))) : (¬ (r1_mode ≤ (1 : Int))) := by
  exact (Or.elim (replay_6508 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (i398 t0))))

-- Checked replay of unit-resolution.
theorem replay_6510 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) (i398 : (¬ (r1_mode ≤ (2 : Int)))) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6507 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6509 r1_mode i398) t0))))

-- Checked replay of unit-resolution.
theorem replay_6511 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) (i398 : (¬ (r1_mode ≤ (2 : Int)))) (i401 : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i402 : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i403 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i400 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : False := by
  exact (Or.elim (replay_6501 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (False.elim (l0 i399))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6506 c3_depth c3_kind c3_sign r1_group r1_level r1_mode i398)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6510 c3_depth c3_kind c3_sign r1_group r1_level r1_mode i398)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i401))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i402))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i403))) (fun t5 => (False.elim (t5 i400))))))))))))))

abbrev shared_expr_Repair100_22 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := ((r1_mode ≤ (2 : Int)) ∨ (¬ (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) ∨ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))))
abbrev formula_2604 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair100_22 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)

-- Checked replay of lemma.
theorem replay_6512 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (formula_2604 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6511 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

theorem propositional_2225 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6513 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ∨ (r1_mode ≥ (4 : Int))) := by
  exact (propositional_2225 (r1_mode ≤ (4 : Int)) (r1_mode ≥ (4 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((c3_node % (2 : Int)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))

theorem propositional_2226 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6514 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ∨ (r1_mode ≤ (2 : Int))) := by
  exact (propositional_2226 (r1_mode ≤ (2 : Int)) (r1_mode ≥ (2 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ((c0_node % (2 : Int)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6515 (r1_mode : Int) (i218 : (r1_mode ≥ (4 : Int))) : (r1_mode ≥ (3 : Int)) := by
  exact (Or.elim (replay_2089 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 i218))))

-- Checked replay of unit-resolution.
theorem replay_6516 (r1_mode : Int) (i218 : (r1_mode ≥ (4 : Int))) : (¬ (r1_mode ≤ (2 : Int))) := by
  exact (Or.elim (replay_6500 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_6515 r1_mode i218)))))

-- Checked replay of unit-resolution.
theorem replay_6517 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) (i218 : (r1_mode ≥ (4 : Int))) : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6514 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6516 r1_mode i218) t0))))

theorem propositional_2227 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6518 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ∨ (r1_mode ≤ (3 : Int))) := by
  exact (propositional_2227 (r1_mode ≤ (3 : Int)) (r1_mode ≥ (3 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ((c0_node % (2 : Int)) ≥ (1 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6519 (r1_mode : Int) (i218 : (r1_mode ≥ (4 : Int))) : (¬ (r1_mode ≤ (3 : Int))) := by
  exact (Or.elim (replay_5725 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 i218))))

-- Checked replay of unit-resolution.
theorem replay_6520 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) (i218 : (r1_mode ≥ (4 : Int))) : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6518 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6519 r1_mode i218) t0))))

-- Checked replay of unit-resolution.
theorem replay_6521 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) (i218 : (r1_mode ≥ (4 : Int))) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) : False := by
  exact (Or.elim (replay_6498 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (fun l0 => (False.elim (l0 i404))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i405))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i406))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_6517 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode i218)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_6520 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode i218)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 i407))) (fun t5 => (False.elim (t5 i408))))))))))))))

abbrev shared_expr_Repair100_23 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := ((¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) ∨ (¬ ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) ∨ (¬ ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))))
abbrev formula_2605 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : Prop := (shared_expr_Repair100_23 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)

-- Checked replay of lemma.
theorem replay_6522 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (formula_2605 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6521 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))))

-- Checked replay of unit-resolution.
theorem replay_6523 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) : (¬ (r1_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_6522 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i404))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i405))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i406))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i407))) (fun t4 => (False.elim (t4 i408))))))))))))

-- Checked replay of unit-resolution.
theorem replay_6524 (c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_2599 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6513 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6523 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode i405 i406 i407 i408 i404) t0))))

theorem propositional_2228 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6525 (c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) ∨ (r1_mode ≥ (5 : Int))) := by
  exact (propositional_2228 (r1_mode ≤ (5 : Int)) (r1_mode ≥ (5 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) ((¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int)))))) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((c3_node % (2 : Int)) ≥ (1 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_6526 (r1_mode : Int) : ((r1_mode ≥ (4 : Int)) ∨ (¬ (r1_mode ≥ (5 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6527 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) : (¬ (r1_mode ≥ (5 : Int))) := by
  exact (Or.elim (replay_6526 r1_mode) (fun l0 => (False.elim ((replay_6523 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode i405 i406 i407 i408 i404) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6528 (c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_2601 c3_depth c3_kind c3_node c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6525 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6527 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode i405 i406 i407 i408 i404) t0))))

-- Checked replay of unit-resolution.
theorem replay_6529 (c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) (i401 : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i402 : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : (r1_mode ≤ (2 : Int)) := by
  exact (Or.elim (replay_6512 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i399))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6528 c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode i405 i406 i407 i408 i404)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i401))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 i402))) (fun t4 => (False.elim (t4 (replay_6524 c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode i405 i406 i407 i408 i404)))))))))))))

-- Checked replay of unit-resolution.
theorem replay_6530 (c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) (i401 : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i402 : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : (¬ (r1_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_6500 r1_mode) (fun l0 => (False.elim (l0 (replay_6529 c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode i405 i406 i407 i408 i404 i401 i402 i399)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6531 (c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode : Int) (i405 : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_878 c0_depth c0_kind c0_sign r1_group r1_level)))) (i406 : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_880 c0_depth c0_kind c0_sign r1_group r1_level)))) (i407 : ((¬ (r1_mode ≤ (4 : Int))) ∨ (¬ (r1_mode ≥ (4 : Int))) ∨ (¬ (formula_886 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i408 : ((¬ (r1_mode ≤ (5 : Int))) ∨ (¬ (r1_mode ≥ (5 : Int))) ∨ (¬ (formula_888 c0_depth c0_kind c0_node c0_sign r1_group r1_level)))) (i404 : (formula_889 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode)) (i401 : ((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_2595 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i402 : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_2597 c3_depth c3_kind c3_node c3_sign r1_group r1_level)))) (i399 : (formula_2602 c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode)) : ((¬ (r1_mode ≤ (3 : Int))) ∨ (¬ (r1_mode ≥ (3 : Int))) ∨ (¬ (formula_884 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6499 c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6530 c0_depth c0_kind c0_node c0_sign c3_depth c3_kind c3_node c3_sign r1_group r1_level r1_mode i405 i406 i407 i408 i404 i401 i402 i399) t0))))

theorem propositional_2229 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ ((¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p10) ∨ (¬ p11))))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6532 (c0_depth c0_kind c0_node c0_sign r1_group r1_level r1_mode : Int) : (((¬ (r1_mode ≤ (2 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int))) ∨ (¬ (formula_882 c0_depth c0_kind c0_node c0_sign r1_group r1_level))) ∨ (r1_mode ≥ (2 : Int))) := by
  exact (propositional_2229 (r1_mode ≤ (2 : Int)) (r1_mode ≥ (2 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (c0_kind ≤ (1 : Int)) (c0_kind ≥ (1 : Int)) ((¬ ((¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (c0_sign ≤ (2 : Int))) ∨ (¬ (c0_sign ≥ (2 : Int)))))) ((c0_node % (2 : Int)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (0 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≤ (1 : Int)) ((r1_level + ((-1 : Int) * c0_depth)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6533 (r1_mode : Int) (i409 : (r1_mode ≥ (2 : Int))) : (r1_mode ≥ (1 : Int)) := by
  exact (Or.elim (replay_2091 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 i409))))

-- Checked replay of unit-resolution.
theorem replay_6534 (r1_mode : Int) (i409 : (r1_mode ≥ (2 : Int))) : (¬ (r1_mode ≤ (0 : Int))) := by
  exact (Or.elim (replay_2092 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_6533 r1_mode i409)))))

-- Checked replay of unit-resolution.
theorem replay_6535 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) (i409 : (r1_mode ≥ (2 : Int))) : ((¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (formula_2591 c3_depth c3_kind c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6502 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6534 r1_mode i409) t0))))

-- Checked replay of th-lemma.
theorem replay_6536 (r1_mode : Int) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6537 (r1_mode : Int) (i409 : (r1_mode ≥ (2 : Int))) : (¬ (r1_mode ≤ (1 : Int))) := by
  exact (Or.elim (replay_6536 r1_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 i409))))

-- Checked replay of unit-resolution.
theorem replay_6538 (c3_depth c3_kind c3_sign r1_group r1_level r1_mode : Int) (i409 : (r1_mode ≥ (2 : Int))) : ((¬ (r1_mode ≤ (1 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int))) ∨ (¬ (formula_2593 c3_depth c3_kind c3_sign r1_group r1_level))) := by
  exact (Or.elim (replay_6507 c3_depth c3_kind c3_sign r1_group r1_level r1_mode) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_6537 r1_mode i409) t0))))

end H4Formal.Generated.Repair
