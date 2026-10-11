import H4Formal.Certificates.CheckedRepair.Repair019

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair020_0 (c0_mode c2_mode : Int) : Prop := ((¬ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))
abbrev formula_645 (c0_mode c2_mode : Int) : Prop := (shared_expr_Repair020_0 c0_mode c2_mode)

theorem propositional_517 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_842 (c0_mode c2_mode : Int) : (formula_645 c0_mode c2_mode) := by
  exact (propositional_517 ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_843 (c0_mode c2_mode : Int) : ((c2_mode ≤ (0 : Int)) ∨ (¬ (c0_mode ≤ (1 : Int))) ∨ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_844 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (c2_mode ≥ (1 : Int)) := by
  exact (Or.elim (replay_578 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim (i71 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_845 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (¬ (c2_mode ≤ (0 : Int))) := by
  exact (Or.elim (replay_217 c2_mode) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_844 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i71)))))

-- Checked replay of unit-resolution.
theorem replay_846 (c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i72 : (c0_mode ≤ (1 : Int))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_843 c0_mode c2_mode) (fun l0 => (False.elim ((replay_845 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i71) l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i72))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_847 (c0_mode c2_mode : Int) : ((¬ (c2_mode ≤ (1 : Int))) ∨ (c0_mode ≤ (0 : Int)) ∨ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_848 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (c2_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_222 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim (i71 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_849 (c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i73 : (¬ (c0_mode ≤ (0 : Int)))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_847 c0_mode c2_mode) (fun l0 => (False.elim (l0 (replay_848 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i71)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i73 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_850 (c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i73 : (¬ (c0_mode ≤ (0 : Int)))) (i72 : (c0_mode ≤ (1 : Int))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (¬ ((¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c2_mode)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_842 c0_mode c2_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_846 c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign i72 i71)))) (fun t1 => (False.elim (t1 (replay_849 c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign i73 i71)))))))

-- Checked replay of unit-resolution.
theorem replay_851 (c0_group c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i74 : ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) (i73 : (¬ (c0_mode ≤ (0 : Int)))) (i72 : (c0_mode ≤ (1 : Int))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (¬ (formula_632 c0_group c0_mode c2_group c2_mode)) := by
  exact (Or.elim (replay_841 c0_group c0_mode c2_group c2_mode) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_850 c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign i73 i72 i71) l1))) (fun t1 => (False.elim (t1 i74))))))

-- Checked replay of unit-resolution.
theorem replay_852 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i74 : ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) (i73 : (¬ (c0_mode ≤ (0 : Int)))) (i75 : (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (i72 : (c0_mode ≤ (1 : Int))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : ((¬ ((c0_level + ((-1 : Int) * c2_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int)))) := by
  exact (Or.elim (replay_840 c0_group c0_level c0_mode c2_group c2_level c2_mode) (fun l0 => (False.elim (l0 i75))) (fun t0 => (Or.elim t0 (fun l1 => (Or.elim l1 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t1 => (False.elim ((replay_851 c0_group c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign i74 i73 i72 i71) t1))))))

-- Checked replay of unit-resolution.
theorem replay_853 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i74 : ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) (i73 : (¬ (c0_mode ≤ (0 : Int)))) (i75 : (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (i72 : (c0_mode ≤ (1 : Int))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (¬ ((c0_level + ((-1 : Int) * c2_level)) ≥ (0 : Int))) := by
  exact (Or.elim (replay_839 c0_group c0_level c0_mode c2_group c2_level c2_mode) (fun l0 => (False.elim (l0 i75))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_852 c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign i74 i73 i75 i72 i71)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_854 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (formula_185 c2_group c2_level r2_depth r2_kind r2_sign) := by
  exact (Or.elim (replay_549 c2_group c2_level c2_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim (i71 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_855 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i77 : ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (¬ (formula_183 c2_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_548 c2_group c2_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim (l0 (replay_854 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i71)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i77))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_856 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i77 : ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : ((r2_depth + ((-1 : Int) * c2_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_802 c2_level r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_855 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i77 i71) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_857 (c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i77 : ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : (¬ ((r2_depth + ((-1 : Int) * c2_level)) ≤ (-1 : Int))) := by
  exact (Or.elim (replay_801 c2_level r2_depth) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_856 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i77 i71)))))

-- Checked replay of th-lemma.
theorem replay_858 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) (i74 : ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) (i73 : (¬ (c0_mode ≤ (0 : Int)))) (i77 : ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) (i75 : (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) (i72 : (c0_mode ≤ (1 : Int))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i71 : (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))))) : False := by
  classical
  have k0 := (replay_853 c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign i74 i73 i75 i72 i71)
  have k1 := i76
  have k2 := (replay_857 c2_group c2_level c2_mode r2_depth r2_kind r2_sign i77 i71)
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair020_1 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : Prop := (((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_185 c2_group c2_level r2_depth r2_kind r2_sign))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ (¬ ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) ∨ (¬ (c0_mode ≤ (1 : Int))) ∨ (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∨ (c0_mode ≤ (0 : Int)))
abbrev formula_646 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Repair020_1 c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign)

-- Checked replay of lemma.
theorem replay_859 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign : Int) : (formula_646 c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_858 c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_kind r2_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (fun q => nc (Or.inl q)))

theorem propositional_518 (p0 p1 p2 : Prop) : ((¬ ((p0 ∧ p1) ∨ ((¬ p0) ∧ p2))) ∨ (¬ p0) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_860 (c0_group c0_level c0_mode c2_group c2_level c2_mode : Int) : ((formula_634 c0_group c0_level c0_mode c2_group c2_level c2_mode) ∨ (¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∨ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) := by
  exact (propositional_518 ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode) (c0_mode ≥ (4 : Int)))

theorem propositional_519 (p0 p1 p2 p3 p4 p5 p6 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_861 (c0_group c0_level r2_depth r2_kind r2_sign : Int) : ((¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ (formula_63 c0_level r2_depth r2_kind r2_sign))) := by
  exact (propositional_519 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) (formula_63 c0_level r2_depth r2_kind r2_sign) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)))

theorem propositional_520 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7)))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_862 (c0_level r2_depth r2_kind r2_sign : Int) : ((formula_63 c0_level r2_depth r2_kind r2_sign) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int))) := by
  exact (propositional_520 (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (-1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_863 (c0_level r2_depth r2_kind r2_sign : Int) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) : (formula_63 c0_level r2_depth r2_kind r2_sign) := by
  exact (Or.elim (replay_862 c0_level r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.inr (Or.inr (Or.inr (Or.inr t103))))))))))))) (fun t0 => (False.elim (i79 t0))))

-- Checked replay of unit-resolution.
theorem replay_864 (c0_group c0_level r2_depth r2_kind r2_sign : Int) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) : (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign)) := by
  exact (Or.elim (replay_861 c0_group c0_level r2_depth r2_kind r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i78))) (fun t1 => (False.elim (t1 (replay_863 c0_level r2_depth r2_kind r2_sign i79)))))))

-- Checked replay of unit-resolution.
theorem replay_865 (c0_group c0_level c0_mode r2_depth r2_kind r2_sign : Int) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) : ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_65 c0_group c0_level r2_depth r2_kind r2_sign))) := by
  exact (Or.elim (replay_627 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_864 c0_group c0_level r2_depth r2_kind r2_sign i78 i79) t0))))

theorem propositional_521 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_866 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) := by
  exact (propositional_521 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_867 (c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_866 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i78))) (fun t1 => (False.elim (t1 (replay_272 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23)))))))

-- Checked replay of unit-resolution.
theorem replay_868 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_72 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_601 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_867 c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78) t0))))

theorem propositional_522 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((¬ p8) ∨ (¬ p9))))) ∨ (¬ p10)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_869 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) := by
  exact (propositional_522 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_870 (c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_869 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i78))) (fun t1 => (False.elim (t1 (replay_272 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23)))))))

-- Checked replay of unit-resolution.
theorem replay_871 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_74 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_615 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_870 c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78) t0))))

theorem propositional_523 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ ((¬ ((¬ p6) ∨ (¬ p7))) ∨ (¬ ((¬ p8) ∨ (¬ p9))))) ∨ (¬ p10)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_872 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) := by
  exact (propositional_523 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_873 (c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_872 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i78))) (fun t1 => (False.elim (t1 (replay_272 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23)))))))

-- Checked replay of unit-resolution.
theorem replay_874 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_76 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_621 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_873 c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78) t0))))

theorem propositional_524 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ (¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((¬ ((¬ p4) ∨ (¬ p5))) ∨ (¬ ((¬ p6) ∨ (¬ p7))))) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_875 (c0_group c0_level r2_depth r2_kind r2_node r2_sign : Int) : ((¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) ∨ (¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) := by
  exact (propositional_524 ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int)))) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((r2_node % (2 : Int)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_876 (c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_875 c0_group c0_level r2_depth r2_kind r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i78))) (fun t1 => (False.elim (t1 (replay_272 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23)))))))

-- Checked replay of unit-resolution.
theorem replay_877 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) : ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_70 c0_group c0_level r2_depth r2_kind r2_node r2_sign))) := by
  exact (Or.elim (replay_609 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.inr (Or.inr t101))))))) (fun t0 => (False.elim ((replay_876 c0_group c0_level r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78) t0))))

-- Checked replay of unit-resolution.
theorem replay_878 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_68 c0_group c0_level r2_depth r2_kind r2_sign)))) := by
  exact (Or.elim (replay_600 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 i52))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_865 c0_group c0_level c0_mode r2_depth r2_kind r2_sign i78 i79)))) (fun t1 => (Or.elim t1 (fun l2 => l2) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_877 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_868 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78)))) (fun t4 => (Or.elim t4 (fun l5 => (False.elim (l5 (replay_871 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78)))) (fun t5 => (False.elim (t5 (replay_874 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78)))))))))))))))

-- Checked replay of unit-resolution.
theorem replay_879 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (c0_mode ≤ (1 : Int)) := by
  exact (Or.elim (replay_599 c0_group c0_level c0_mode r2_depth r2_kind r2_sign) (fun l0 => (False.elim ((replay_878 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78 i79 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_880 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (c0_mode ≥ (2 : Int))) := by
  exact (Or.elim (replay_598 c0_mode) (fun l0 => (False.elim (l0 (replay_879 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78 i79 i52)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_881 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (c0_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_597 c0_mode) (fun l0 => (False.elim ((replay_880 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78 i79 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_882 (c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (¬ (c0_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_596 c0_mode) (fun l0 => (False.elim ((replay_881 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78 i79 i52) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_883 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i66 : ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_757 c0_group c0_level c0_mode c2_group c2_level c2_mode) (fun l0 => (False.elim (l0 i66))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim ((replay_882 c0_group c0_level c0_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78 i79 i52) t1))))))

-- Checked replay of unit-resolution.
theorem replay_884 (c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i78 : ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) (i66 : ((((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int))) ∧ (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode)) ∨ ((¬ ((c0_mode ≥ (4 : Int)) ↔ (c2_mode ≥ (4 : Int)))) ∧ (c0_mode ≥ (4 : Int))))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i52 : (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) : (formula_633 c0_group c0_level c0_mode c2_group c2_level c2_mode) := by
  exact (Or.elim (replay_860 c0_group c0_level c0_mode c2_group c2_level c2_mode) (fun l0 => (False.elim (l0 i66))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_883 c0_group c0_level c0_mode c2_group c2_level c2_mode r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i23 i78 i66 i79 i52)))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_885 (c0_group c2_group : Int) : ((c0_group ≤ (1 : Int)) ∨ (¬ (c2_group ≤ (2 : Int))) ∨ ((c0_group + ((-1 : Int) * c2_group)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_886 (c0_level r1_depth r2_depth : Int) : ((¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_887 (c0_level r1_depth r2_depth : Int) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) : ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_886 c0_level r1_depth r2_depth) (fun l0 => (False.elim (l0 i80))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i79 l1))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_888 (h r1_depth r2_depth : Int) : ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)) ∨ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_889 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign) := by
  exact (Or.elim (replay_563 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (i81 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_890 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (¬ (formula_188 c2_level r2_depth r2_kind r2_node r2_sign)) := by
  exact (Or.elim (replay_564 c2_group c2_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim (l0 (replay_889 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i81)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i34 l1))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_891 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) := by
  exact (Or.elim (replay_763 c2_level r2_depth r2_kind r2_node r2_sign) (fun l0 => (False.elim ((replay_890 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i81) l0))) (fun t0 => (Or.elim t0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))))

-- Checked replay of unit-resolution.
theorem replay_892 (c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))))) := by
  exact (Or.elim (replay_690 r2_sign) (fun l0 => (False.elim (l0 i59))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_891 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i34 i81)))))))

-- Checked replay of unit-resolution.
theorem replay_893 (c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i82 : (formula_170 h r2_depth r2_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : (¬ ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_691 h r2_depth r2_sign) (fun l0 => (False.elim (l0 i82))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim ((replay_892 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign i59 i34 i81) t1))))))

-- Checked replay of unit-resolution.
theorem replay_894 (c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i82 : (formula_170 h r2_depth r2_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_808 h r2_depth) (fun l0 => (False.elim ((replay_893 c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign i59 i82 i34 i81) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_895 (c2_group c2_level c2_mode h r1_depth r2_depth r2_kind r2_node r2_sign : Int) (i59 : ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) (i82 : (formula_170 h r2_depth r2_sign)) (i34 : (¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int)))))) (i39 : (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (-1 : Int)))) (i81 : (¬ ((¬ (c2_mode ≤ (3 : Int))) ∨ (¬ (c2_mode ≥ (3 : Int))) ∨ (¬ (formula_189 c2_group c2_level r2_depth r2_kind r2_node r2_sign))))) : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_888 h r1_depth r2_depth) (fun l0 => (False.elim (l0 (replay_894 c2_group c2_level c2_mode h r2_depth r2_kind r2_node r2_sign i59 i82 i34 i81)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i39 l1))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_896 (c1_level h r3_depth : Int) : ((¬ ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_525 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p2 : p2 <;> simp [case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_897 (r3_sign : Int) : (((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))) ∨ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))) := by
  exact (propositional_525 (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))

abbrev shared_expr_Repair020_2 (h r3_depth r3_sign : Int) : Prop := (((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))) ∧ ((¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int)))))))
abbrev shared_expr_Repair020_3 (h r3_depth r3_sign : Int) : Prop := ((shared_expr_Repair020_2 h r3_depth r3_sign) ∨ ((¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))))) ∧ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))))
abbrev formula_647 (h r3_depth r3_sign : Int) : Prop := (shared_expr_Repair020_3 h r3_depth r3_sign)

abbrev shared_expr_Repair020_4 (h r3_depth r3_sign : Int) : Prop := ((¬ (formula_647 h r3_depth r3_sign)) ∨ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))
abbrev formula_648 (h r3_depth r3_sign : Int) : Prop := (shared_expr_Repair020_4 h r3_depth r3_sign)

theorem propositional_526 (p0 p1 p2 p3 p4 p5 : Prop) : ((¬ ((p0 ∧ ((¬ ((¬ p1) ∨ (¬ p2))) ∨ (¬ ((¬ p3) ∨ (¬ p4))))) ∨ ((¬ p0) ∧ (¬ p5)))) ∨ p0 ∨ (¬ p5)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_898 (h r3_depth r3_sign : Int) : (formula_648 h r3_depth r3_sign) := by
  exact (propositional_526 ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))) (r3_sign ≤ (0 : Int)) (r3_sign ≥ (0 : Int)) (r3_sign ≤ (1 : Int)) (r3_sign ≥ (1 : Int)) ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))

abbrev shared_expr_Repair020_5 (h r3_depth : Int) : Prop := ((¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))))
abbrev formula_649 (h r3_depth : Int) : Prop := (shared_expr_Repair020_5 h r3_depth)

theorem propositional_527 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_899 (h r3_depth : Int) : (formula_649 h r3_depth) := by
  exact (propositional_527 ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)))

abbrev shared_expr_Repair020_6 (c1_level h r1_depth r2_depth r3_depth : Int) : Prop := (((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) ∨ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ∨ (¬ ((r2_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
abbrev formula_650 (c1_level h r1_depth r2_depth r3_depth : Int) : Prop := (shared_expr_Repair020_6 c1_level h r1_depth r2_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_900 (c1_level h r1_depth r2_depth r3_depth : Int) : (formula_650 c1_level h r1_depth r2_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_901 (c0_level c1_level r2_depth : Int) : ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_528 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_902 (c0_level c1_level : Int) : (((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ∨ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) := by
  exact (propositional_528 ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))

abbrev shared_expr_Repair020_7 (c0_group c0_mode c1_group c1_mode : Int) : Prop := ((((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ∧ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int))) ∨ (¬ ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int))))) ∧ (¬ ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))))
abbrev formula_651 (c0_group c0_mode c1_group c1_mode : Int) : Prop := (shared_expr_Repair020_7 c0_group c0_mode c1_group c1_mode)

abbrev shared_expr_Repair020_8 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ∧ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) ∧ (formula_651 c0_group c0_mode c1_group c1_mode)))
abbrev formula_652 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (shared_expr_Repair020_8 c0_group c0_level c0_mode c1_group c1_level c1_mode)

abbrev shared_expr_Repair020_9 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := ((¬ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ (¬ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))
abbrev formula_653 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : Prop := (shared_expr_Repair020_9 c0_group c0_level c0_mode c1_group c1_level c1_mode)

theorem propositional_529 (p0 p1 p2 p3 p4 : Prop) : ((¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ ((((¬ p2) ∨ (¬ p3)) ∧ (¬ p3)) ∨ ((¬ ((¬ p2) ∨ (¬ p3))) ∧ (¬ p4)))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_903 (c0_group c0_level c0_mode c1_group c1_level c1_mode : Int) : (formula_653 c0_group c0_level c0_mode c1_group c1_level c1_mode) := by
  exact (propositional_529 ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)))) ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ((c0_mode + ((-1 : Int) * c1_mode)) ≤ (0 : Int)) ((c0_mode + ((-1 : Int) * c1_mode)) ≥ (0 : Int)) ((c0_group + ((-1 : Int) * c1_group)) ≥ (0 : Int)))

-- Checked replay of th-lemma.
theorem replay_904 (c0_level c1_level r2_depth : Int) : (((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_905 (c1_level h r2_depth : Int) : ((¬ ((r2_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_906 (c0_level h r1_depth r2_depth : Int) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i83 : (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)))) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) : False := by
  classical
  have k0 := i83
  have k1 := i84
  have k2 := i79
  have k3 := i80
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair020_10 (c0_level h r1_depth r2_depth : Int) : Prop := ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))))
abbrev formula_654 (c0_level h r1_depth r2_depth : Int) : Prop := (shared_expr_Repair020_10 c0_level h r1_depth r2_depth)

-- Checked replay of lemma.
theorem replay_907 (c0_level h r1_depth r2_depth : Int) : (formula_654 c0_level h r1_depth r2_depth) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_906 c0_level h r1_depth r2_depth (Classical.byContradiction (fun q => nc (Or.inl q))) (fun q => nc (Or.inr (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr q))))) (fun q => nc (Or.inr (Or.inr (Or.inl q)))))

-- Checked replay of unit-resolution.
theorem replay_908 (c0_level h r1_depth r2_depth : Int) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_907 c0_level h r1_depth r2_depth) (fun l0 => (False.elim (l0 i84))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (i79 l2))) (fun t2 => (False.elim (t2 i80))))))))

-- Checked replay of unit-resolution.
theorem replay_909 (c0_level c1_level h r1_depth r2_depth : Int) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) : (¬ ((r2_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int))) := by
  exact (Or.elim (replay_905 c1_level h r2_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i85))) (fun t1 => (False.elim (t1 (replay_908 c0_level h r1_depth r2_depth i84 i80 i79)))))))

-- Checked replay of unit-resolution.
theorem replay_910 (c0_level c1_level h r1_depth r2_depth : Int) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_904 c0_level c1_level r2_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i76))) (fun t1 => (False.elim ((replay_909 c0_level c1_level h r1_depth r2_depth i85 i84 i80 i79) t1))))))

-- Checked replay of unit-resolution.
theorem replay_911 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth : Int) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : (¬ ((¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_903 c0_group c0_level c0_mode c1_group c1_level c1_mode) (fun l0 => (False.elim (l0 i86))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_910 c0_level c1_level h r1_depth r2_depth i85 i84 i80 i79 i76)))))))

-- Checked replay of unit-resolution.
theorem replay_912 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth : Int) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_902 c0_level c1_level) (fun l0 => (False.elim ((replay_911 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth i85 i84 i86 i80 i79 i76) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_913 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth : Int) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((r2_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_901 c0_level c1_level r2_depth) (fun l0 => (False.elim (l0 (replay_912 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth i85 i84 i86 i80 i79 i76)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i76))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_914 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth : Int) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i87 : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_900 c1_level h r1_depth r2_depth r3_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (i87 l1))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_913 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth i85 i84 i86 i80 i79 i76)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_887 c0_level r1_depth r2_depth i80 i79)))) (fun t3 => (False.elim (t3 i84))))))))))

-- Checked replay of unit-resolution.
theorem replay_915 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth : Int) (i88 : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i87 : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) : (¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))))) := by
  exact (Or.elim (replay_899 h r3_depth) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_914 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth i85 i84 i86 i80 i79 i76 i87)))) (fun t1 => (False.elim (t1 i88))))))

-- Checked replay of unit-resolution.
theorem replay_916 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_sign : Int) (i88 : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i89 : (formula_647 h r3_depth r3_sign)) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i87 : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) : (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_898 h r3_depth r3_sign) (fun l0 => (False.elim (l0 i89))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim ((replay_915 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth i88 i85 i84 i86 i80 i79 i76 i87) l1))) (fun t1 => t1))))

abbrev shared_expr_Repair020_11 (c0_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))))
abbrev formula_655 (c0_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair020_11 c0_level r3_depth r3_kind r3_sign)

abbrev shared_expr_Repair020_12 (c0_level r3_depth r3_kind r3_sign : Int) : Prop := ((¬ (formula_655 c0_level r3_depth r3_kind r3_sign)) ∨ (¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))))
abbrev formula_656 (c0_level r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair020_12 c0_level r3_depth r3_kind r3_sign)

theorem propositional_530 (p0 p1 p2 p3 p4 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4))) ∨ (¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_917 (c0_level r3_depth r3_kind r3_sign : Int) : (formula_656 c0_level r3_depth r3_kind r3_sign) := by
  exact (propositional_530 (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int)))))))

-- Checked replay of th-lemma.
theorem replay_918 (c0_level c1_level r3_depth : Int) : ((¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

abbrev shared_expr_Repair020_13 (c1_level h r1_depth r2_depth r3_depth : Int) : Prop := ((¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ∨ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int)) ∨ (¬ ((r2_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ (¬ ((r1_depth + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))))
abbrev formula_657 (c1_level h r1_depth r2_depth r3_depth : Int) : Prop := (shared_expr_Repair020_13 c1_level h r1_depth r2_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_919 (c1_level h r1_depth r2_depth r3_depth : Int) : (formula_657 c1_level h r1_depth r2_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_920 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth : Int) (i88 : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((r3_depth + ((-1 : Int) * c1_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_919 c1_level h r1_depth r2_depth r3_depth) (fun l0 => (False.elim (l0 i88))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_913 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth i85 i84 i86 i80 i79 i76)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_887 c0_level r1_depth r2_depth i80 i79)))) (fun t3 => (False.elim (t3 i84))))))))))

-- Checked replay of unit-resolution.
theorem replay_921 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth : Int) (i88 : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) : ((r3_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int)) := by
  exact (Or.elim (replay_918 c0_level c1_level r3_depth) (fun l0 => (False.elim (l0 (replay_920 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth i88 i85 i84 i86 i80 i79 i76)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_910 c0_level c1_level h r1_depth r2_depth i85 i84 i80 i79 i76)))) (fun t1 => t1))))

-- Checked replay of th-lemma.
theorem replay_922 (c0_level c1_level r3_depth : Int) : (((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ∨ (¬ ((c0_level + ((-1 : Int) * c1_level)) ≤ (0 : Int))) ∨ ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_923 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth : Int) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i87 : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) : ((r3_depth + ((-1 : Int) * c0_level)) ≥ (0 : Int)) := by
  exact (Or.elim (replay_922 c0_level c1_level r3_depth) (fun l0 => (False.elim (i87 l0))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_912 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth i85 i84 i86 i80 i79 i76)))) (fun t1 => t1))))

-- Checked replay of unit-resolution.
theorem replay_924 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign : Int) (i88 : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i91 : (r3_kind ≥ (1 : Int))) (i92 : (r3_kind ≤ (1 : Int))) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i90 : (formula_655 c0_level r3_depth r3_kind r3_sign)) (i87 : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) : (¬ ((¬ ((¬ (r3_sign ≤ (1 : Int))) ∨ (¬ (r3_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r3_sign ≤ (2 : Int))) ∨ (¬ (r3_sign ≥ (2 : Int))))))) := by
  exact (Or.elim (replay_917 c0_level r3_depth r3_kind r3_sign) (fun l0 => (False.elim (l0 i90))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i92))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 i91))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 (replay_921 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth i88 i85 i84 i86 i80 i79 i76)))) (fun t3 => (Or.elim t3 (fun l4 => (False.elim (l4 (replay_923 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth i85 i84 i86 i80 i79 i76 i87)))) (fun t4 => t4))))))))))

-- Checked replay of unit-resolution.
theorem replay_925 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign : Int) (i88 : ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) (i85 : ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) (i84 : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) (i91 : (r3_kind ≥ (1 : Int))) (i92 : (r3_kind ≤ (1 : Int))) (i89 : (formula_647 h r3_depth r3_sign)) (i86 : (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) (i80 : ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i79 : (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)))) (i76 : ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) (i90 : (formula_655 c0_level r3_depth r3_kind r3_sign)) (i87 : (¬ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)))) : False := by
  exact (Or.elim (replay_897 r3_sign) (fun l0 => (False.elim ((replay_924 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign i88 i85 i84 i91 i92 i86 i80 i79 i76 i90 i87) l0))) (fun t0 => (False.elim ((replay_916 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_sign i88 i85 i84 i89 i86 i80 i79 i76 i87) t0))))

abbrev shared_expr_Repair020_14 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (formula_647 h r3_depth r3_sign)) ∨ (¬ (formula_655 c0_level r3_depth r3_kind r3_sign)) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ (r3_kind ≤ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ∨ ((r3_depth + ((-1 : Int) * c1_level)) ≤ (-1 : Int)) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ (formula_652 c0_group c0_level c0_mode c1_group c1_level c1_mode)) ∨ (¬ ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ (¬ ((r1_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))))
abbrev formula_658 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign : Int) : Prop := (shared_expr_Repair020_14 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign)

-- Checked replay of lemma.
theorem replay_926 (c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign : Int) : (formula_658 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_925 c0_group c0_level c0_mode c1_group c1_level c1_mode h r1_depth r2_depth r3_depth r3_kind r3_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inl q))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q))))))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))

abbrev shared_expr_Repair020_15 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((¬ (r3_mode ≤ (0 : Int))) ∨ (¬ (r3_mode ≥ (0 : Int))) ∨ (¬ (r3_level ≤ (0 : Int))) ∨ (¬ (r3_level ≥ (0 : Int))) ∨ (¬ (r3_group ≤ (0 : Int))) ∨ (¬ (r3_group ≥ (0 : Int))) ∨ (¬ (r3_depth ≥ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int))) ∨ (¬ (r3_kind ≤ (1 : Int))) ∨ (¬ (r3_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int))) ∨ (¬ ((¬ (r3_depth ≤ (0 : Int))) ∨ (¬ (r3_depth ≥ (0 : Int))) ∨ (¬ ((¬ (r3_node ≤ (0 : Int))) ∨ (¬ (r3_node ≥ (0 : Int))))))) ∨ (¬ (formula_647 h r3_depth r3_sign)))
abbrev formula_659 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair020_15 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem propositional_531 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p7))))) ∨ (¬ p13)) ∨ p13) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_927 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_659 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ∨ (formula_647 h r3_depth r3_sign)) := by
  exact (propositional_531 (r3_mode ≤ (0 : Int)) (r3_mode ≥ (0 : Int)) (r3_level ≤ (0 : Int)) (r3_level ≥ (0 : Int)) (r3_group ≤ (0 : Int)) (r3_group ≥ (0 : Int)) (r3_depth ≥ (0 : Int)) (r3_node ≥ (0 : Int)) (r3_kind ≤ (1 : Int)) (r3_kind ≥ (1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≥ (0 : Int)) (r3_depth ≤ (0 : Int)) (r3_node ≤ (0 : Int)) (formula_647 h r3_depth r3_sign))

abbrev shared_expr_Repair020_16 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((r3_kind = (0 : Int)) ∧ (r3_mode ≥ (0 : Int)) ∧ (r3_mode < (6 : Int)) ∧ (r3_level ≥ (1 : Int)) ∧ (r3_level ≤ h) ∧ ((r3_group = (1 : Int)) ∨ (r3_group = (2 : Int))) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int)))
abbrev formula_660 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair020_16 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair020_17 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((r3_kind = (0 : Int)) ∧ (r3_mode ≥ (0 : Int)) ∧ (¬ ((6 : Int) ≤ r3_mode)) ∧ (r3_level ≥ (1 : Int)) ∧ (r3_level ≤ h) ∧ ((r3_group = (1 : Int)) ∨ (r3_group = (2 : Int))) ∧ (r3_depth = (0 : Int)) ∧ (r3_node = (0 : Int)) ∧ (r3_sign = (0 : Int)))
abbrev formula_661 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair020_17 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_532 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : ((p0 ∧ (¬ p1) ∧ p2 ∧ (¬ p3) ∧ (¬ p4) ∧ p5 ∧ p6 ∧ p7 ∧ p8) ↔ (p0 ∧ (¬ p1) ∧ (¬ (¬ p2)) ∧ (¬ p3) ∧ (¬ p4) ∧ p5 ∧ p6 ∧ p7 ∧ p8)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2642 (r3_mode : Int) : (r3_mode ≥ (0 : Int)) ↔ (¬ ((r3_mode) ≤ (-1 : Int))) := by
  omega

theorem normalization_2643 (r3_mode : Int) : (r3_mode < (6 : Int)) ↔ ((r3_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_2644 (r3_level : Int) : (r3_level ≥ (1 : Int)) ↔ (¬ ((r3_level) ≤ (0 : Int))) := by
  omega

theorem normalization_2645 (h r3_level : Int) : (r3_level ≤ h) ↔ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2646 (r3_group : Int) : (r3_group = (1 : Int)) ↔ (((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) := by
  omega

theorem normalization_2647 (r3_group : Int) : (r3_group = (2 : Int)) ↔ (((r3_group) ≤ (2 : Int)) ∧ (¬ ((r3_group) ≤ (1 : Int)))) := by
  omega

theorem normalization_2648 (r3_group : Int) : ((r3_group = (1 : Int)) ∨ (r3_group = (2 : Int))) ↔ ((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∨ (((r3_group) ≤ (2 : Int)) ∧ (¬ ((r3_group) ≤ (1 : Int))))) := (or_congr (normalization_2646 r3_group) (normalization_2647 r3_group))

theorem normalization_2649 (r3_depth : Int) : (r3_depth = (0 : Int)) ↔ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2650 (r3_node : Int) : (r3_node = (0 : Int)) ↔ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) := by
  omega

abbrev shared_expr_Repair020_18 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (¬ ((r3_mode) ≤ (-1 : Int))) ∧ ((r3_mode) ≤ (5 : Int)) ∧ (¬ ((r3_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∨ (((r3_group) ≤ (2 : Int)) ∧ (¬ ((r3_group) ≤ (1 : Int))))) ∧ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) ∧ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) ∧ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))))
theorem normalization_2651 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_660 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair020_18 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (and_congr (normalization_1241 r3_kind) (and_congr (normalization_2642 r3_mode) (and_congr (normalization_2643 r3_mode) (and_congr (normalization_2644 r3_level) (and_congr (normalization_2645 h r3_level) (and_congr (normalization_2648 r3_group) (and_congr (normalization_2649 r3_depth) (and_congr (normalization_2650 r3_node) (normalization_1259 r3_sign)))))))))

theorem normalization_2652 (r3_mode : Int) : ((6 : Int) ≤ r3_mode) ↔ (¬ ((r3_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2653 (r3_mode : Int) : (¬ ((6 : Int) ≤ r3_mode)) ↔ (¬ (¬ ((r3_mode) ≤ (5 : Int)))) := (not_congr (normalization_2652 r3_mode))

abbrev shared_expr_Repair020_19 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ∧ (¬ ((r3_mode) ≤ (-1 : Int))) ∧ (¬ (¬ ((r3_mode) ≤ (5 : Int)))) ∧ (¬ ((r3_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int))) ∧ ((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∨ (((r3_group) ≤ (2 : Int)) ∧ (¬ ((r3_group) ≤ (1 : Int))))) ∧ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) ∧ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) ∧ (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))))
theorem normalization_2654 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_661 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair020_19 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (and_congr (normalization_1241 r3_kind) (and_congr (normalization_2642 r3_mode) (and_congr (normalization_2653 r3_mode) (and_congr (normalization_2644 r3_level) (and_congr (normalization_2645 h r3_level) (and_congr (normalization_2648 r3_group) (and_congr (normalization_2649 r3_depth) (and_congr (normalization_2650 r3_node) (normalization_1259 r3_sign)))))))))

theorem normalization_2655 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_660 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_661 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair020_18 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair020_19 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2651 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2654 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_928 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_660 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_661 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_532 (((r3_kind) ≤ (0 : Int)) ∧ (¬ ((r3_kind) ≤ (-1 : Int)))) ((r3_mode) ≤ (-1 : Int)) ((r3_mode) ≤ (5 : Int)) ((r3_level) ≤ (0 : Int)) ((h + ((-1 : Int) * r3_level)) ≤ (-1 : Int)) ((((r3_group) ≤ (1 : Int)) ∧ (¬ ((r3_group) ≤ (0 : Int)))) ∨ (((r3_group) ≤ (2 : Int)) ∧ (¬ ((r3_group) ≤ (1 : Int))))) (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) (((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2655 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

abbrev shared_expr_Repair020_20 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((r3_kind = (1 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth ≥ (0 : Int)) ∧ (r3_depth ≤ h) ∧ (r3_node ≥ (0 : Int)) ∧ ((r3_depth = (0 : Int)) → (r3_node = (0 : Int))) ∧ (((r3_depth = h) ∧ (r3_sign = (2 : Int))) ∨ ((¬ (r3_depth = h)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (1 : Int))))))
abbrev formula_662 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair020_20 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

abbrev shared_expr_Repair020_21 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((r3_kind = (1 : Int)) ∧ (r3_mode = (0 : Int)) ∧ (r3_level = (0 : Int)) ∧ (r3_group = (0 : Int)) ∧ (r3_depth ≥ (0 : Int)) ∧ (r3_depth ≤ h) ∧ (r3_node ≥ (0 : Int)) ∧ ((¬ (r3_depth = (0 : Int))) ∨ (r3_node = (0 : Int))) ∧ (((r3_depth = h) ∧ (r3_sign = (2 : Int))) ∨ ((¬ (r3_depth = h)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (1 : Int))))))
abbrev formula_663 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := (shared_expr_Repair020_21 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)

theorem normalized_533 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ (¬ p5) ∧ (¬ p6) ∧ (p7 → p8) ∧ p9) ↔ (p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ (¬ p5) ∧ (¬ p6) ∧ ((¬ p7) ∨ p8) ∧ p9)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2656 (r3_mode : Int) : (r3_mode = (0 : Int)) ↔ (((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2657 (r3_level : Int) : (r3_level = (0 : Int)) ↔ (((r3_level) ≤ (0 : Int)) ∧ (¬ ((r3_level) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2658 (r3_group : Int) : (r3_group = (0 : Int)) ↔ (((r3_group) ≤ (0 : Int)) ∧ (¬ ((r3_group) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2659 (r3_depth : Int) : (r3_depth ≥ (0 : Int)) ↔ (¬ ((r3_depth) ≤ (-1 : Int))) := by
  omega

theorem normalization_2660 (h r3_depth : Int) : (r3_depth ≤ h) ↔ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2661 (r3_node : Int) : (r3_node ≥ (0 : Int)) ↔ (¬ ((r3_node) ≤ (-1 : Int))) := by
  omega

theorem normalization_2662 (r3_depth r3_node : Int) : ((r3_depth = (0 : Int)) → (r3_node = (0 : Int))) ↔ ((((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) → (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int))))) := (imp_congr (normalization_2649 r3_depth) (normalization_2650 r3_node))

theorem normalization_2663 (h r3_depth : Int) : (r3_depth = h) ↔ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_2664 (r3_sign : Int) : (r3_sign = (2 : Int)) ↔ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int)))) := by
  omega

theorem normalization_2665 (r3_sign : Int) : (r3_sign = (1 : Int)) ↔ (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int)))) := by
  omega

theorem normalization_2666 (r3_sign : Int) : ((r3_sign = (0 : Int)) ∨ (r3_sign = (1 : Int))) ↔ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int))))) := (or_congr (normalization_1259 r3_sign) (normalization_2665 r3_sign))

abbrev shared_expr_Repair020_22 (h r3_depth r3_sign : Int) : Prop := ((¬ ((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int)))) ∧ ((((r3_sign) ≤ (0 : Int)) ∧ (¬ ((r3_sign) ≤ (-1 : Int)))) ∨ (((r3_sign) ≤ (1 : Int)) ∧ (¬ ((r3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair020_23 (h r3_depth r3_sign : Int) : Prop := ((((¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∧ (((r3_sign) ≤ (2 : Int)) ∧ (¬ ((r3_sign) ≤ (1 : Int))))) ∨ (shared_expr_Repair020_22 h r3_depth r3_sign))
theorem normalization_2667 (h r3_depth r3_sign : Int) : (((r3_depth = h) ∧ (r3_sign = (2 : Int))) ∨ ((¬ (r3_depth = h)) ∧ ((r3_sign = (0 : Int)) ∨ (r3_sign = (1 : Int))))) ↔ (shared_expr_Repair020_23 h r3_depth r3_sign) := (or_congr (and_congr (normalization_2663 h r3_depth) (normalization_2664 r3_sign)) (and_congr (not_congr (normalization_2663 h r3_depth)) (normalization_2666 r3_sign)))

abbrev shared_expr_Repair020_24 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ (((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (((r3_level) ≤ (0 : Int)) ∧ (¬ ((r3_level) ≤ (-1 : Int)))) ∧ (((r3_group) ≤ (0 : Int)) ∧ (¬ ((r3_group) ≤ (-1 : Int)))) ∧ (¬ ((r3_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ (¬ ((r3_node) ≤ (-1 : Int))) ∧ ((((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) → (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair020_23 h r3_depth r3_sign))
theorem normalization_2668 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_662 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair020_24 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (and_congr (normalization_1254 r3_kind) (and_congr (normalization_2656 r3_mode) (and_congr (normalization_2657 r3_level) (and_congr (normalization_2658 r3_group) (and_congr (normalization_2659 r3_depth) (and_congr (normalization_2660 h r3_depth) (and_congr (normalization_2661 r3_node) (and_congr (normalization_2662 r3_depth r3_node) (normalization_2667 h r3_depth r3_sign)))))))))

theorem normalization_2669 (r3_depth : Int) : (¬ (r3_depth = (0 : Int))) ↔ (¬ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int))))) := (not_congr (normalization_2649 r3_depth))

theorem normalization_2670 (r3_depth r3_node : Int) : ((¬ (r3_depth = (0 : Int))) ∨ (r3_node = (0 : Int))) ↔ ((¬ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int))))) ∨ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int))))) := (or_congr (normalization_2669 r3_depth) (normalization_2650 r3_node))

abbrev shared_expr_Repair020_25 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : Prop := ((((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) ∧ (((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) ∧ (((r3_level) ≤ (0 : Int)) ∧ (¬ ((r3_level) ≤ (-1 : Int)))) ∧ (((r3_group) ≤ (0 : Int)) ∧ (¬ ((r3_group) ≤ (-1 : Int)))) ∧ (¬ ((r3_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int))) ∧ (¬ ((r3_node) ≤ (-1 : Int))) ∧ ((¬ (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int))))) ∨ (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair020_23 h r3_depth r3_sign))
theorem normalization_2671 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : (formula_663 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair020_25 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) := (and_congr (normalization_1254 r3_kind) (and_congr (normalization_2656 r3_mode) (and_congr (normalization_2657 r3_level) (and_congr (normalization_2658 r3_group) (and_congr (normalization_2659 r3_depth) (and_congr (normalization_2660 h r3_depth) (and_congr (normalization_2661 r3_node) (and_congr (normalization_2670 r3_depth r3_node) (normalization_2667 h r3_depth r3_sign)))))))))

theorem normalization_2672 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_662 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_663 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) ↔ ((shared_expr_Repair020_24 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (shared_expr_Repair020_25 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := (iff_congr (normalization_2668 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) (normalization_2671 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign))

-- Checked replay of rewrite.
theorem replay_929 (h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) : ((formula_662 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) ↔ (formula_663 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) := by
  classical
  have ht := (normalized_533 (((r3_kind) ≤ (1 : Int)) ∧ (¬ ((r3_kind) ≤ (0 : Int)))) (((r3_mode) ≤ (0 : Int)) ∧ (¬ ((r3_mode) ≤ (-1 : Int)))) (((r3_level) ≤ (0 : Int)) ∧ (¬ ((r3_level) ≤ (-1 : Int)))) (((r3_group) ≤ (0 : Int)) ∧ (¬ ((r3_group) ≤ (-1 : Int)))) ((r3_depth) ≤ (-1 : Int)) ((h + ((-1 : Int) * r3_depth)) ≤ (-1 : Int)) ((r3_node) ≤ (-1 : Int)) (((r3_depth) ≤ (0 : Int)) ∧ (¬ ((r3_depth) ≤ (-1 : Int)))) (((r3_node) ≤ (0 : Int)) ∧ (¬ ((r3_node) ≤ (-1 : Int)))) (shared_expr_Repair020_23 h r3_depth r3_sign))
  have hn := ht
  exact Iff.mpr (normalization_2672 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign) hn

end H4Formal.Generated.Repair
