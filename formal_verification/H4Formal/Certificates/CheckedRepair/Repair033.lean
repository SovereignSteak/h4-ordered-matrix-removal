import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair032

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

abbrev shared_expr_Repair033_0 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ (¬ (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_721 c0_group c0_level r3_depth r3_kind r3_sign)))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ∨ (¬ (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) ∨ (¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_700 c2_group c2_level r1_depth r1_kind r1_sign)))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (r1_mode ≥ (4 : Int)) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_638 h r1_depth r1_sign)) ∨ (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))) ∨ (formula_634 c0_group c0_level c0_mode c2_group c2_level c2_mode) ∨ (¬ (c2_mode ≤ (5 : Int))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_733 c2_group c2_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_713 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_710 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ (c0_mode ≤ (5 : Int))) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_745 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_737 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_group ≤ (2 : Int))) ∨ (¬ (c2_group ≥ (2 : Int))))))) ∨ (¬ ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ (formula_696 c0_group c0_level c0_mode c1_group c1_level c1_mode) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_694 c0_group c0_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_group ≤ (2 : Int))) ∨ (¬ (c0_group ≥ (2 : Int))))))) ∨ (c0_level ≤ (0 : Int)))
abbrev formula_760 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair033_0 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_2061 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) : (formula_760 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_2060 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i10 i93 i62 i23 (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q)))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))))))))))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))))

abbrev shared_expr_Repair033_1 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((r1_kind = (0 : Int)) ∧ (r1_mode ≥ (0 : Int)) ∧ (r1_mode < (6 : Int)) ∧ (r1_level ≥ (1 : Int)) ∧ (r1_level ≤ h) ∧ ((r1_group = (1 : Int)) ∨ (r1_group = (2 : Int))) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int)))
abbrev formula_761 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_1 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_2 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((r1_kind = (0 : Int)) ∧ (r1_mode ≥ (0 : Int)) ∧ (¬ ((6 : Int) ≤ r1_mode)) ∧ (r1_level ≥ (1 : Int)) ∧ (r1_level ≤ h) ∧ ((r1_group = (1 : Int)) ∨ (r1_group = (2 : Int))) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int)))
abbrev formula_762 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_2 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_709 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : ((p0 ∧ (¬ p1) ∧ p2 ∧ (¬ p3) ∧ (¬ p4) ∧ p5 ∧ p6 ∧ p7 ∧ p8) ↔ (p0 ∧ (¬ p1) ∧ (¬ (¬ p2)) ∧ (¬ p3) ∧ (¬ p4) ∧ p5 ∧ p6 ∧ p7 ∧ p8)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2757 (r1_mode : Int) : (r1_mode ≥ (0 : Int)) ↔ (¬ ((r1_mode) ≤ (-1 : Int))) := by
  omega

theorem normalization_2758 (r1_mode : Int) : (r1_mode < (6 : Int)) ↔ ((r1_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_2759 (r1_level : Int) : (r1_level ≥ (1 : Int)) ↔ (¬ ((r1_level) ≤ (0 : Int))) := by
  omega

theorem normalization_2760 (h r1_level : Int) : (r1_level ≤ h) ↔ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2761 (r1_group : Int) : (r1_group = (1 : Int)) ↔ (((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) := by
  omega

theorem normalization_2762 (r1_group : Int) : (r1_group = (2 : Int)) ↔ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int)))) := by
  omega

theorem normalization_2763 (r1_group : Int) : ((r1_group = (1 : Int)) ∨ (r1_group = (2 : Int))) ↔ ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∨ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int))))) := (or_congr (normalization_2761 r1_group) (normalization_2762 r1_group))

theorem normalization_2764 (r1_depth : Int) : (r1_depth = (0 : Int)) ↔ (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2765 (r1_node : Int) : (r1_node = (0 : Int)) ↔ (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int)))) := by
  omega

abbrev shared_expr_Repair033_3 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (¬ ((r1_mode) ≤ (-1 : Int))) ∧ ((r1_mode) ≤ (5 : Int)) ∧ (¬ ((r1_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∨ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int))))) ∧ (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) ∧ (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int)))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))))
theorem normalization_2766 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_761 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_3 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (and_congr (normalization_2270 r1_kind) (and_congr (normalization_2757 r1_mode) (and_congr (normalization_2758 r1_mode) (and_congr (normalization_2759 r1_level) (and_congr (normalization_2760 h r1_level) (and_congr (normalization_2763 r1_group) (and_congr (normalization_2764 r1_depth) (and_congr (normalization_2765 r1_node) (normalization_2287 r1_sign)))))))))

theorem normalization_2767 (r1_mode : Int) : ((6 : Int) ≤ r1_mode) ↔ (¬ ((r1_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2768 (r1_mode : Int) : (¬ ((6 : Int) ≤ r1_mode)) ↔ (¬ (¬ ((r1_mode) ≤ (5 : Int)))) := (not_congr (normalization_2767 r1_mode))

abbrev shared_expr_Repair033_4 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ∧ (¬ ((r1_mode) ≤ (-1 : Int))) ∧ (¬ (¬ ((r1_mode) ≤ (5 : Int)))) ∧ (¬ ((r1_level) ≤ (0 : Int))) ∧ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) ∧ ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∨ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int))))) ∧ (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) ∧ (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int)))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))))
theorem normalization_2769 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_762 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (and_congr (normalization_2270 r1_kind) (and_congr (normalization_2757 r1_mode) (and_congr (normalization_2768 r1_mode) (and_congr (normalization_2759 r1_level) (and_congr (normalization_2760 h r1_level) (and_congr (normalization_2763 r1_group) (and_congr (normalization_2764 r1_depth) (and_congr (normalization_2765 r1_node) (normalization_2287 r1_sign)))))))))

theorem normalization_2770 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_761 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_762 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_3 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2766 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2769 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2062 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_761 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_762 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_709 (((r1_kind) ≤ (0 : Int)) ∧ (¬ ((r1_kind) ≤ (-1 : Int)))) ((r1_mode) ≤ (-1 : Int)) ((r1_mode) ≤ (5 : Int)) ((r1_level) ≤ (0 : Int)) ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((((r1_group) ≤ (1 : Int)) ∧ (¬ ((r1_group) ≤ (0 : Int)))) ∨ (((r1_group) ≤ (2 : Int)) ∧ (¬ ((r1_group) ≤ (1 : Int))))) (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int)))) (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Repair033_5 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((r1_kind = (1 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth ≥ (0 : Int)) ∧ (r1_depth ≤ h) ∧ (r1_node ≥ (0 : Int)) ∧ ((r1_depth = (0 : Int)) → (r1_node = (0 : Int))) ∧ (((r1_depth = h) ∧ (r1_sign = (2 : Int))) ∨ ((¬ (r1_depth = h)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (1 : Int))))))
abbrev formula_763 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_5 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_6 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((r1_kind = (1 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth ≥ (0 : Int)) ∧ (r1_depth ≤ h) ∧ (r1_node ≥ (0 : Int)) ∧ ((¬ (r1_depth = (0 : Int))) ∨ (r1_node = (0 : Int))) ∧ (((r1_depth = h) ∧ (r1_sign = (2 : Int))) ∨ ((¬ (r1_depth = h)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (1 : Int))))))
abbrev formula_764 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_6 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_710 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : ((p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ (¬ p5) ∧ (¬ p6) ∧ (p7 → p8) ∧ p9) ↔ (p0 ∧ p1 ∧ p2 ∧ p3 ∧ (¬ p4) ∧ (¬ p5) ∧ (¬ p6) ∧ ((¬ p7) ∨ p8) ∧ p9)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2771 (r1_mode : Int) : (r1_mode = (0 : Int)) ↔ (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2772 (r1_level : Int) : (r1_level = (0 : Int)) ↔ (((r1_level) ≤ (0 : Int)) ∧ (¬ ((r1_level) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2773 (r1_group : Int) : (r1_group = (0 : Int)) ↔ (((r1_group) ≤ (0 : Int)) ∧ (¬ ((r1_group) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2774 (r1_depth : Int) : (r1_depth ≥ (0 : Int)) ↔ (¬ ((r1_depth) ≤ (-1 : Int))) := by
  omega

theorem normalization_2775 (h r1_depth : Int) : (r1_depth ≤ h) ↔ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2776 (r1_node : Int) : (r1_node ≥ (0 : Int)) ↔ (¬ ((r1_node) ≤ (-1 : Int))) := by
  omega

theorem normalization_2777 (r1_depth r1_node : Int) : ((r1_depth = (0 : Int)) → (r1_node = (0 : Int))) ↔ ((((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) → (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int))))) := (imp_congr (normalization_2764 r1_depth) (normalization_2765 r1_node))

theorem normalization_2778 (h r1_depth : Int) : (r1_depth = h) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := by
  omega

theorem normalization_2779 (r1_sign : Int) : (r1_sign = (2 : Int)) ↔ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int)))) := by
  omega

theorem normalization_2780 (r1_sign : Int) : ((r1_sign = (0 : Int)) ∨ (r1_sign = (1 : Int))) ↔ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int))))) := (or_congr (normalization_2287 r1_sign) (normalization_2479 r1_sign))

abbrev shared_expr_Repair033_7 (h r1_depth r1_sign : Int) : Prop := ((¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)))) ∧ ((((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (((r1_sign) ≤ (1 : Int)) ∧ (¬ ((r1_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair033_8 (h r1_depth r1_sign : Int) : Prop := ((((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∧ (((r1_sign) ≤ (2 : Int)) ∧ (¬ ((r1_sign) ≤ (1 : Int))))) ∨ (shared_expr_Repair033_7 h r1_depth r1_sign))
theorem normalization_2781 (h r1_depth r1_sign : Int) : (((r1_depth = h) ∧ (r1_sign = (2 : Int))) ∨ ((¬ (r1_depth = h)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (1 : Int))))) ↔ (shared_expr_Repair033_8 h r1_depth r1_sign) := (or_congr (and_congr (normalization_2778 h r1_depth) (normalization_2779 r1_sign)) (and_congr (not_congr (normalization_2778 h r1_depth)) (normalization_2780 r1_sign)))

abbrev shared_expr_Repair033_9 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (((r1_level) ≤ (0 : Int)) ∧ (¬ ((r1_level) ≤ (-1 : Int)))) ∧ (((r1_group) ≤ (0 : Int)) ∧ (¬ ((r1_group) ≤ (-1 : Int)))) ∧ (¬ ((r1_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ (¬ ((r1_node) ≤ (-1 : Int))) ∧ ((((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) → (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair033_8 h r1_depth r1_sign))
theorem normalization_2782 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_763 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_9 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (and_congr (normalization_2282 r1_kind) (and_congr (normalization_2771 r1_mode) (and_congr (normalization_2772 r1_level) (and_congr (normalization_2773 r1_group) (and_congr (normalization_2774 r1_depth) (and_congr (normalization_2775 h r1_depth) (and_congr (normalization_2776 r1_node) (and_congr (normalization_2777 r1_depth r1_node) (normalization_2781 h r1_depth r1_sign)))))))))

theorem normalization_2783 (r1_depth : Int) : (¬ (r1_depth = (0 : Int))) ↔ (¬ (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int))))) := (not_congr (normalization_2764 r1_depth))

theorem normalization_2784 (r1_depth r1_node : Int) : ((¬ (r1_depth = (0 : Int))) ∨ (r1_node = (0 : Int))) ↔ ((¬ (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int))))) ∨ (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int))))) := (or_congr (normalization_2783 r1_depth) (normalization_2765 r1_node))

abbrev shared_expr_Repair033_10 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) ∧ (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (((r1_level) ≤ (0 : Int)) ∧ (¬ ((r1_level) ≤ (-1 : Int)))) ∧ (((r1_group) ≤ (0 : Int)) ∧ (¬ ((r1_group) ≤ (-1 : Int)))) ∧ (¬ ((r1_depth) ≤ (-1 : Int))) ∧ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) ∧ (¬ ((r1_node) ≤ (-1 : Int))) ∧ ((¬ (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int))))) ∨ (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int))))) ∧ (shared_expr_Repair033_8 h r1_depth r1_sign))
theorem normalization_2785 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_764 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (and_congr (normalization_2282 r1_kind) (and_congr (normalization_2771 r1_mode) (and_congr (normalization_2772 r1_level) (and_congr (normalization_2773 r1_group) (and_congr (normalization_2774 r1_depth) (and_congr (normalization_2775 h r1_depth) (and_congr (normalization_2776 r1_node) (and_congr (normalization_2784 r1_depth r1_node) (normalization_2781 h r1_depth r1_sign)))))))))

theorem normalization_2786 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_763 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_764 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_9 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2782 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2785 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2063 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_763 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_764 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_710 (((r1_kind) ≤ (1 : Int)) ∧ (¬ ((r1_kind) ≤ (0 : Int)))) (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) (((r1_level) ≤ (0 : Int)) ∧ (¬ ((r1_level) ≤ (-1 : Int)))) (((r1_group) ≤ (0 : Int)) ∧ (¬ ((r1_group) ≤ (-1 : Int)))) ((r1_depth) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((r1_node) ≤ (-1 : Int)) (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int)))) (shared_expr_Repair033_8 h r1_depth r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_2786 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Repair033_11 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_761 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (formula_763 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ ((r1_kind = (2 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int))))
abbrev formula_765 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_11 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_12 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((formula_762 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (formula_764 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ ((r1_kind = (2 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int))))
abbrev formula_766 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_12 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_711 (p0 p1 p2 p3 p4 : Prop) : (((p0 ↔ p1) ∧ (p2 ↔ p3)) → ((p0 ∨ p2 ∨ p4) ↔ (p1 ∨ p3 ∨ p4))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair033_13 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((((r1_kind) ≤ (2 : Int)) ∧ (¬ ((r1_kind) ≤ (1 : Int)))) ∧ (((r1_mode) ≤ (0 : Int)) ∧ (¬ ((r1_mode) ≤ (-1 : Int)))) ∧ (((r1_level) ≤ (0 : Int)) ∧ (¬ ((r1_level) ≤ (-1 : Int)))) ∧ (((r1_group) ≤ (0 : Int)) ∧ (¬ ((r1_group) ≤ (-1 : Int)))) ∧ (((r1_depth) ≤ (0 : Int)) ∧ (¬ ((r1_depth) ≤ (-1 : Int)))) ∧ (((r1_node) ≤ (0 : Int)) ∧ (¬ ((r1_node) ≤ (-1 : Int)))) ∧ (((r1_sign) ≤ (0 : Int)) ∧ (¬ ((r1_sign) ≤ (-1 : Int)))))
theorem normalization_2787 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((r1_kind = (2 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int))) ↔ (shared_expr_Repair033_13 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (and_congr (normalization_2284 r1_kind) (and_congr (normalization_2771 r1_mode) (and_congr (normalization_2772 r1_level) (and_congr (normalization_2773 r1_group) (and_congr (normalization_2764 r1_depth) (and_congr (normalization_2765 r1_node) (normalization_2287 r1_sign)))))))

abbrev shared_expr_Repair033_14 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair033_3 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (shared_expr_Repair033_9 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (shared_expr_Repair033_13 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2788 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_14 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2766 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (or_congr (normalization_2782 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2787 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))

abbrev shared_expr_Repair033_15 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (shared_expr_Repair033_13 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2789 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_766 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_15 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2769 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (or_congr (normalization_2785 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2787 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))

theorem normalization_2790 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_766 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_14 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_15 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2788 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2789 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of monotonicity.
theorem replay_2064 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_766 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_711 (shared_expr_Repair033_3 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_9 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_13 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : ((shared_expr_Repair033_3 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
    exact Iff.mp (normalization_2770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2062 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have n1 : ((shared_expr_Repair033_9 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
    exact Iff.mp (normalization_2786 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2063 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2790 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

abbrev shared_expr_Repair033_16 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r1_kind = (2 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int))) ∨ (formula_762 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (formula_764 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_767 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_16 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_712 (p0 p1 p2 : Prop) : ((p0 ∨ p1 ∨ p2) ↔ (p2 ∨ p0 ∨ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair033_17 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((shared_expr_Repair033_13 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
theorem normalization_2791 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2787 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (or_congr (normalization_2769 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2785 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))

theorem normalization_2792 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_766 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_15 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2789 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2791 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2065 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_766 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_712 (shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_13 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_2792 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

theorem normalized_713 (p0 p1 p2 : Prop) : (((p0 ↔ p1) ∧ (p1 ↔ p2)) → (p0 ↔ p2)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2793 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_14 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2788 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2791 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of trans.
theorem replay_2066 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_713 (shared_expr_Repair033_14 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_15 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have n0 : ((shared_expr_Repair033_14 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_15 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
    exact Iff.mp (normalization_2790 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2064 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have n1 : ((shared_expr_Repair033_15 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
    exact Iff.mp (normalization_2792 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2065 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_2793 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2067 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2066 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) i146

theorem normalized_714 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2794 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2791 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2791 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2068 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_714 (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_2794 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2069 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2068 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2067 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146)

abbrev shared_expr_Repair033_18 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((r1_kind = (0 : Int)) ∧ (r1_mode ≥ (0 : Int)) ∧ (¬ (r1_mode ≥ (6 : Int))) ∧ (r1_level ≥ (1 : Int)) ∧ ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int)) ∧ ((r1_group = (1 : Int)) ∨ (r1_group = (2 : Int))) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int)))
abbrev formula_768 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_18 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_19 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((r1_kind = (1 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth ≥ (0 : Int)) ∧ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ∧ (r1_node ≥ (0 : Int)) ∧ ((¬ (r1_depth = (0 : Int))) ∨ (r1_node = (0 : Int))) ∧ (((r1_depth = h) ∧ (r1_sign = (2 : Int))) ∨ ((¬ (r1_depth = h)) ∧ ((r1_sign = (0 : Int)) ∨ (r1_sign = (1 : Int))))))
abbrev formula_769 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_19 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_20 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (((r1_kind = (2 : Int)) ∧ (r1_mode = (0 : Int)) ∧ (r1_level = (0 : Int)) ∧ (r1_group = (0 : Int)) ∧ (r1_depth = (0 : Int)) ∧ (r1_node = (0 : Int)) ∧ (r1_sign = (0 : Int))) ∨ (formula_768 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (formula_769 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
abbrev formula_770 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_20 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_715 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2795 (r1_mode : Int) : (r1_mode ≥ (6 : Int)) ↔ (¬ ((r1_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2796 (r1_mode : Int) : (¬ (r1_mode ≥ (6 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (5 : Int)))) := (not_congr (normalization_2795 r1_mode))

theorem normalization_2797 (h r1_level : Int) : ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int)) ↔ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2798 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_768 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_4 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (and_congr (normalization_2270 r1_kind) (and_congr (normalization_2757 r1_mode) (and_congr (normalization_2796 r1_mode) (and_congr (normalization_2759 r1_level) (and_congr (normalization_2797 h r1_level) (and_congr (normalization_2763 r1_group) (and_congr (normalization_2764 r1_depth) (and_congr (normalization_2765 r1_node) (normalization_2287 r1_sign)))))))))

theorem normalization_2799 (h r1_depth : Int) : ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) ↔ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))) := by
  omega

theorem normalization_2800 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_769 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_10 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (and_congr (normalization_2282 r1_kind) (and_congr (normalization_2771 r1_mode) (and_congr (normalization_2772 r1_level) (and_congr (normalization_2773 r1_group) (and_congr (normalization_2774 r1_depth) (and_congr (normalization_2799 h r1_depth) (and_congr (normalization_2776 r1_node) (and_congr (normalization_2784 r1_depth r1_node) (normalization_2781 h r1_depth r1_sign)))))))))

theorem normalization_2801 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2787 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (or_congr (normalization_2798 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2800 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))

theorem normalization_2802 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2791 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2801 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2070 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_767 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_715 (shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))
  have hn := ht
  exact Iff.mpr (normalization_2802 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2071 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2070 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2069 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146)

abbrev shared_expr_Repair033_21 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_group ≤ (0 : Int))) ∨ (¬ (r1_group ≥ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int))) ∨ (¬ (r1_node ≤ (0 : Int))) ∨ (¬ (r1_level ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_depth ≤ (0 : Int))) ∨ (¬ (r1_depth ≥ (0 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))) ∨ (¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_level ≤ (0 : Int))))
abbrev formula_771 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_21 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_22 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((r1_mode ≥ (6 : Int)) ∨ (¬ (r1_sign ≥ (0 : Int))) ∨ (¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int))) ∨ (¬ (r1_node ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))) ∨ (¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_depth ≤ (0 : Int))) ∨ (¬ (r1_depth ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) ∨ (¬ (r1_level ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int))))
abbrev formula_772 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_22 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_23 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ (r1_group ≤ (0 : Int))) ∨ (¬ (r1_group ≥ (0 : Int))) ∨ (¬ (r1_mode ≥ (0 : Int))) ∨ (¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int))) ∨ (¬ (r1_level ≥ (0 : Int))) ∨ (¬ (r1_depth ≥ (0 : Int))) ∨ (¬ (r1_level ≤ (0 : Int))) ∨ (¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ∨ (¬ ((¬ (r1_depth ≤ (0 : Int))) ∨ (¬ (r1_depth ≥ (0 : Int))) ∨ (¬ ((¬ (r1_node ≤ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int))))))) ∨ (¬ (formula_638 h r1_depth r1_sign)))
abbrev formula_773 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_23 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

abbrev shared_expr_Repair033_24 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ∨ (¬ (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ∨ (¬ (formula_773 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))
abbrev formula_774 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := (shared_expr_Repair033_24 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)

theorem normalized_716 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 : Prop) : ((((p0 ∧ (¬ p1)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p14 ∧ (¬ p15)) ∧ (¬ p3) ∧ (¬ (¬ p16)) ∧ (¬ p4) ∧ (¬ p17) ∧ ((p18 ∧ (¬ p6)) ∨ (p19 ∧ (¬ p18))) ∧ (p8 ∧ (¬ p9)) ∧ (p10 ∧ (¬ p11)) ∧ (p12 ∧ (¬ p13))) ∨ ((p1 ∧ (¬ p14)) ∧ (p2 ∧ (¬ p3)) ∧ (p4 ∧ (¬ p5)) ∧ (p6 ∧ (¬ p7)) ∧ (¬ p9) ∧ (¬ p20) ∧ (¬ p11) ∧ ((¬ (p8 ∧ (¬ p9))) ∨ (p10 ∧ (¬ p11))) ∧ ((((¬ p20) ∧ p21) ∧ (p22 ∧ (¬ p23))) ∨ ((¬ ((¬ p20) ∧ p21)) ∧ ((p12 ∧ (¬ p13)) ∨ (p23 ∧ (¬ p12))))))) ↔ ((¬ ((¬ (¬ p13)) ∨ (¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ (¬ p3)) ∨ (¬ p2) ∨ (¬ (¬ p11)) ∨ (¬ p10) ∨ (¬ (¬ p5)) ∨ (¬ p12) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ (¬ p1)) ∨ (¬ p0) ∨ (¬ p4))) ∨ (¬ ((¬ p16) ∨ (¬ (¬ p13)) ∨ (¬ p14) ∨ (¬ (¬ p3)) ∨ (¬ (¬ p11)) ∨ (¬ p10) ∨ (¬ (¬ p15)) ∨ (¬ p12) ∨ (¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ ((¬ ((¬ p18) ∨ (¬ (¬ p6)))) ∨ (¬ ((¬ p19) ∨ (¬ (¬ p18)))))) ∨ (¬ (¬ p4)) ∨ (¬ (¬ p17)))) ∨ (¬ ((¬ p6) ∨ (¬ (¬ p7)) ∨ (¬ (¬ p3)) ∨ (¬ p2) ∨ (¬ (¬ p11)) ∨ (¬ (¬ p5)) ∨ (¬ (¬ p9)) ∨ (¬ p4) ∨ (¬ p1) ∨ (¬ (¬ p14)) ∨ (¬ (¬ p20)) ∨ (¬ ((¬ p8) ∨ (¬ (¬ p9)) ∨ (¬ ((¬ p10) ∨ (¬ (¬ p11)))))) ∨ (¬ ((((¬ p21) ∨ (¬ (¬ p20))) ∧ ((¬ ((¬ p12) ∨ (¬ (¬ p13)))) ∨ (¬ ((¬ p23) ∨ (¬ (¬ p12)))))) ∨ ((¬ ((¬ p21) ∨ (¬ (¬ p20)))) ∧ (¬ ((¬ p22) ∨ (¬ (¬ p23))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2803 (r1_group : Int) : (r1_group ≤ (0 : Int)) ↔ ((r1_group) ≤ (0 : Int)) := by
  omega

theorem normalization_2804 (r1_group : Int) : (¬ (r1_group ≤ (0 : Int))) ↔ (¬ ((r1_group) ≤ (0 : Int))) := (not_congr (normalization_2803 r1_group))

theorem normalization_2805 (r1_group : Int) : (r1_group ≥ (0 : Int)) ↔ (¬ ((r1_group) ≤ (-1 : Int))) := by
  omega

theorem normalization_2806 (r1_group : Int) : (¬ (r1_group ≥ (0 : Int))) ↔ (¬ (¬ ((r1_group) ≤ (-1 : Int)))) := (not_congr (normalization_2805 r1_group))

theorem normalization_2807 (r1_mode : Int) : (¬ (r1_mode ≥ (0 : Int))) ↔ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) := (not_congr (normalization_2757 r1_mode))

theorem normalization_2808 (r1_mode : Int) : (r1_mode ≤ (0 : Int)) ↔ ((r1_mode) ≤ (0 : Int)) := by
  omega

theorem normalization_2809 (r1_mode : Int) : (¬ (r1_mode ≤ (0 : Int))) ↔ (¬ ((r1_mode) ≤ (0 : Int))) := (not_congr (normalization_2808 r1_mode))

theorem normalization_2810 (r1_node : Int) : (¬ (r1_node ≥ (0 : Int))) ↔ (¬ (¬ ((r1_node) ≤ (-1 : Int)))) := (not_congr (normalization_2776 r1_node))

theorem normalization_2811 (r1_node : Int) : (r1_node ≤ (0 : Int)) ↔ ((r1_node) ≤ (0 : Int)) := by
  omega

theorem normalization_2812 (r1_node : Int) : (¬ (r1_node ≤ (0 : Int))) ↔ (¬ ((r1_node) ≤ (0 : Int))) := (not_congr (normalization_2811 r1_node))

theorem normalization_2813 (r1_level : Int) : (r1_level ≥ (0 : Int)) ↔ (¬ ((r1_level) ≤ (-1 : Int))) := by
  omega

theorem normalization_2814 (r1_level : Int) : (¬ (r1_level ≥ (0 : Int))) ↔ (¬ (¬ ((r1_level) ≤ (-1 : Int)))) := (not_congr (normalization_2813 r1_level))

theorem normalization_2815 (r1_depth : Int) : (r1_depth ≤ (0 : Int)) ↔ ((r1_depth) ≤ (0 : Int)) := by
  omega

theorem normalization_2816 (r1_depth : Int) : (¬ (r1_depth ≤ (0 : Int))) ↔ (¬ ((r1_depth) ≤ (0 : Int))) := (not_congr (normalization_2815 r1_depth))

theorem normalization_2817 (r1_depth : Int) : (¬ (r1_depth ≥ (0 : Int))) ↔ (¬ (¬ ((r1_depth) ≤ (-1 : Int)))) := (not_congr (normalization_2774 r1_depth))

theorem normalization_2818 (r1_level : Int) : (r1_level ≤ (0 : Int)) ↔ ((r1_level) ≤ (0 : Int)) := by
  omega

theorem normalization_2819 (r1_level : Int) : (¬ (r1_level ≤ (0 : Int))) ↔ (¬ ((r1_level) ≤ (0 : Int))) := (not_congr (normalization_2818 r1_level))

abbrev shared_expr_Repair033_25 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_group) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int)))) ∨ (¬ ((r1_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_level) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((r1_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r1_kind) ≤ (1 : Int)))) ∨ (¬ ((r1_kind) ≤ (2 : Int))) ∨ (¬ ((r1_level) ≤ (0 : Int))))
theorem normalization_2820 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_25 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2435 r1_sign) (or_congr (normalization_2804 r1_group) (or_congr (normalization_2806 r1_group) (or_congr (normalization_2807 r1_mode) (or_congr (normalization_2809 r1_mode) (or_congr (normalization_2810 r1_node) (or_congr (normalization_2812 r1_node) (or_congr (normalization_2814 r1_level) (or_congr (normalization_2433 r1_sign) (or_congr (normalization_2816 r1_depth) (or_congr (normalization_2817 r1_depth) (or_congr (normalization_2412 r1_kind) (or_congr (normalization_2410 r1_kind) (normalization_2819 r1_level))))))))))))))

theorem normalization_2821 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (¬ (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ (¬ (shared_expr_Repair033_25 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (not_congr (normalization_2820 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

theorem normalization_2822 (r1_group : Int) : (r1_group ≤ (1 : Int)) ↔ ((r1_group) ≤ (1 : Int)) := by
  omega

theorem normalization_2823 (r1_group : Int) : (¬ (r1_group ≤ (1 : Int))) ↔ (¬ ((r1_group) ≤ (1 : Int))) := (not_congr (normalization_2822 r1_group))

theorem normalization_2824 (r1_group : Int) : (r1_group ≥ (1 : Int)) ↔ (¬ ((r1_group) ≤ (0 : Int))) := by
  omega

theorem normalization_2825 (r1_group : Int) : (¬ (r1_group ≥ (1 : Int))) ↔ (¬ (¬ ((r1_group) ≤ (0 : Int)))) := (not_congr (normalization_2824 r1_group))

theorem normalization_2826 (r1_group : Int) : ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int)))) ↔ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int))))) := (or_congr (normalization_2823 r1_group) (normalization_2825 r1_group))

theorem normalization_2827 (r1_group : Int) : (¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ↔ (¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) := (not_congr (normalization_2826 r1_group))

theorem normalization_2828 (r1_group : Int) : (r1_group ≤ (2 : Int)) ↔ ((r1_group) ≤ (2 : Int)) := by
  omega

theorem normalization_2829 (r1_group : Int) : (¬ (r1_group ≤ (2 : Int))) ↔ (¬ ((r1_group) ≤ (2 : Int))) := (not_congr (normalization_2828 r1_group))

theorem normalization_2830 (r1_group : Int) : (r1_group ≥ (2 : Int)) ↔ (¬ ((r1_group) ≤ (1 : Int))) := by
  omega

theorem normalization_2831 (r1_group : Int) : (¬ (r1_group ≥ (2 : Int))) ↔ (¬ (¬ ((r1_group) ≤ (1 : Int)))) := (not_congr (normalization_2830 r1_group))

theorem normalization_2832 (r1_group : Int) : ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))) ↔ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))) := (or_congr (normalization_2829 r1_group) (normalization_2831 r1_group))

theorem normalization_2833 (r1_group : Int) : (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))) ↔ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int)))))) := (not_congr (normalization_2832 r1_group))

theorem normalization_2834 (r1_group : Int) : ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int)))))) ↔ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int))))))) := (or_congr (normalization_2827 r1_group) (normalization_2833 r1_group))

theorem normalization_2835 (r1_group : Int) : (¬ ((¬ ((¬ (r1_group ≤ (1 : Int))) ∨ (¬ (r1_group ≥ (1 : Int))))) ∨ (¬ ((¬ (r1_group ≤ (2 : Int))) ∨ (¬ (r1_group ≥ (2 : Int))))))) ↔ (¬ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int)))))))) := (not_congr (normalization_2834 r1_group))

theorem normalization_2836 (r1_level : Int) : (¬ (r1_level ≥ (1 : Int))) ↔ (¬ (¬ ((r1_level) ≤ (0 : Int)))) := (not_congr (normalization_2759 r1_level))

theorem normalization_2837 (h r1_level : Int) : (¬ ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))) := (not_congr (normalization_2797 h r1_level))

abbrev shared_expr_Repair033_26 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ ((r1_mode) ≤ (5 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))) ∨ (¬ ((r1_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int)))) ∨ (¬ ((r1_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (-1 : Int)))) ∨ (¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ ((r1_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((¬ ((r1_group) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (0 : Int)))))) ∨ (¬ ((¬ ((r1_group) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (1 : Int)))))))) ∨ (¬ (¬ ((r1_level) ≤ (0 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)))))
theorem normalization_2838 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_26 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2795 r1_mode) (or_congr (normalization_2435 r1_sign) (or_congr (normalization_2376 r1_kind) (or_congr (normalization_2807 r1_mode) (or_congr (normalization_2810 r1_node) (or_congr (normalization_2812 r1_node) (or_congr (normalization_2377 r1_kind) (or_congr (normalization_2433 r1_sign) (or_congr (normalization_2816 r1_depth) (or_congr (normalization_2817 r1_depth) (or_congr (normalization_2835 r1_group) (or_congr (normalization_2836 r1_level) (normalization_2837 h r1_level)))))))))))))

theorem normalization_2839 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (¬ (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ (¬ (shared_expr_Repair033_26 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (not_congr (normalization_2838 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

theorem normalization_2840 (r1_kind : Int) : (r1_kind ≤ (1 : Int)) ↔ ((r1_kind) ≤ (1 : Int)) := by
  omega

theorem normalization_2841 (r1_kind : Int) : (¬ (r1_kind ≤ (1 : Int))) ↔ (¬ ((r1_kind) ≤ (1 : Int))) := (not_congr (normalization_2840 r1_kind))

theorem normalization_2842 (r1_kind : Int) : (r1_kind ≥ (1 : Int)) ↔ (¬ ((r1_kind) ≤ (0 : Int))) := by
  omega

theorem normalization_2843 (r1_kind : Int) : (¬ (r1_kind ≥ (1 : Int))) ↔ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) := (not_congr (normalization_2842 r1_kind))

theorem normalization_2844 (h r1_depth : Int) : (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ↔ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) := (not_congr (normalization_2799 h r1_depth))

theorem normalization_2845 (r1_node : Int) : ((¬ (r1_node ≤ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int)))) ↔ ((¬ ((r1_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int))))) := (or_congr (normalization_2812 r1_node) (normalization_2810 r1_node))

theorem normalization_2846 (r1_node : Int) : (¬ ((¬ (r1_node ≤ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int))))) ↔ (¬ ((¬ ((r1_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int)))))) := (not_congr (normalization_2845 r1_node))

theorem normalization_2847 (r1_depth r1_node : Int) : ((¬ (r1_depth ≤ (0 : Int))) ∨ (¬ (r1_depth ≥ (0 : Int))) ∨ (¬ ((¬ (r1_node ≤ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int)))))) ↔ ((¬ ((r1_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r1_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int))))))) := (or_congr (normalization_2816 r1_depth) (or_congr (normalization_2817 r1_depth) (normalization_2846 r1_node)))

theorem normalization_2848 (r1_depth r1_node : Int) : (¬ ((¬ (r1_depth ≤ (0 : Int))) ∨ (¬ (r1_depth ≥ (0 : Int))) ∨ (¬ ((¬ (r1_node ≤ (0 : Int))) ∨ (¬ (r1_node ≥ (0 : Int))))))) ↔ (¬ ((¬ ((r1_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r1_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int)))))))) := (not_congr (normalization_2847 r1_depth r1_node))

theorem normalization_2849 (h r1_depth : Int) : ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ↔ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) := by
  omega

theorem normalization_2850 (h r1_depth : Int) : (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ↔ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) := (not_congr (normalization_2849 h r1_depth))

theorem normalization_2851 (h r1_depth : Int) : ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)))) ↔ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) := (or_congr (normalization_2850 h r1_depth) (normalization_2844 h r1_depth))

theorem normalization_2852 (r1_sign : Int) : ((¬ ((¬ (r1_sign ≤ (0 : Int))) ∨ (¬ (r1_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r1_sign ≤ (1 : Int))) ∨ (¬ (r1_sign ≥ (1 : Int)))))) ↔ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))) := (or_congr (normalization_2437 r1_sign) (normalization_2618 r1_sign))

theorem normalization_2853 (r1_sign : Int) : (r1_sign ≤ (2 : Int)) ↔ ((r1_sign) ≤ (2 : Int)) := by
  omega

theorem normalization_2854 (r1_sign : Int) : (¬ (r1_sign ≤ (2 : Int))) ↔ (¬ ((r1_sign) ≤ (2 : Int))) := (not_congr (normalization_2853 r1_sign))

theorem normalization_2855 (r1_sign : Int) : (r1_sign ≥ (2 : Int)) ↔ (¬ ((r1_sign) ≤ (1 : Int))) := by
  omega

theorem normalization_2856 (r1_sign : Int) : (¬ (r1_sign ≥ (2 : Int))) ↔ (¬ (¬ ((r1_sign) ≤ (1 : Int)))) := (not_congr (normalization_2855 r1_sign))

theorem normalization_2857 (r1_sign : Int) : ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int)))) ↔ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))) := (or_congr (normalization_2854 r1_sign) (normalization_2856 r1_sign))

theorem normalization_2858 (r1_sign : Int) : (¬ ((¬ (r1_sign ≤ (2 : Int))) ∨ (¬ (r1_sign ≥ (2 : Int))))) ↔ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int)))))) := (not_congr (normalization_2857 r1_sign))

abbrev shared_expr_Repair033_27 (h r1_depth r1_sign : Int) : Prop := (((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int))))) ∧ ((¬ ((¬ ((r1_sign) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (-1 : Int)))))) ∨ (¬ ((¬ ((r1_sign) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (0 : Int))))))))
abbrev shared_expr_Repair033_28 (h r1_depth r1_sign : Int) : Prop := ((shared_expr_Repair033_27 h r1_depth r1_sign) ∨ ((¬ ((¬ ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))))) ∧ (¬ ((¬ ((r1_sign) ≤ (2 : Int))) ∨ (¬ (¬ ((r1_sign) ≤ (1 : Int))))))))
theorem normalization_2859 (h r1_depth r1_sign : Int) : (formula_638 h r1_depth r1_sign) ↔ (shared_expr_Repair033_28 h r1_depth r1_sign) := (or_congr (and_congr (normalization_2851 h r1_depth) (normalization_2852 r1_sign)) (and_congr (not_congr (normalization_2851 h r1_depth)) (normalization_2858 r1_sign)))

theorem normalization_2860 (h r1_depth r1_sign : Int) : (¬ (formula_638 h r1_depth r1_sign)) ↔ (¬ (shared_expr_Repair033_28 h r1_depth r1_sign)) := (not_congr (normalization_2859 h r1_depth r1_sign))

abbrev shared_expr_Repair033_29 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ ((r1_group) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_group) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r1_mode) ≤ (-1 : Int)))) ∨ (¬ ((r1_mode) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r1_level) ≤ (-1 : Int)))) ∨ (¬ (¬ ((r1_depth) ≤ (-1 : Int)))) ∨ (¬ ((r1_level) ≤ (0 : Int))) ∨ (¬ ((r1_kind) ≤ (1 : Int))) ∨ (¬ (¬ ((r1_kind) ≤ (0 : Int)))) ∨ (¬ (¬ ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r1_depth) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_depth) ≤ (-1 : Int)))) ∨ (¬ ((¬ ((r1_node) ≤ (0 : Int))) ∨ (¬ (¬ ((r1_node) ≤ (-1 : Int)))))))) ∨ (¬ (shared_expr_Repair033_28 h r1_depth r1_sign)))
theorem normalization_2861 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_773 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_29 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2804 r1_group) (or_congr (normalization_2806 r1_group) (or_congr (normalization_2807 r1_mode) (or_congr (normalization_2809 r1_mode) (or_congr (normalization_2810 r1_node) (or_congr (normalization_2814 r1_level) (or_congr (normalization_2817 r1_depth) (or_congr (normalization_2819 r1_level) (or_congr (normalization_2841 r1_kind) (or_congr (normalization_2843 r1_kind) (or_congr (normalization_2844 h r1_depth) (or_congr (normalization_2848 r1_depth r1_node) (normalization_2860 h r1_depth r1_sign)))))))))))))

theorem normalization_2862 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (¬ (formula_773 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ (¬ (shared_expr_Repair033_29 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (not_congr (normalization_2861 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

abbrev shared_expr_Repair033_30 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : Prop := ((¬ (shared_expr_Repair033_25 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ∨ (¬ (shared_expr_Repair033_26 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ∨ (¬ (shared_expr_Repair033_29 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))
theorem normalization_2863 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : (formula_774 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_30 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := (or_congr (normalization_2821 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (or_congr (normalization_2839 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2862 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)))

theorem normalization_2864 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_774 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) ↔ ((shared_expr_Repair033_17 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (shared_expr_Repair033_30 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := (iff_congr (normalization_2801 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (normalization_2863 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))

-- Checked replay of rewrite.
theorem replay_2072 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_770 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ↔ (formula_774 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) := by
  classical
  have ht := (normalized_716 ((r1_kind) ≤ (2 : Int)) ((r1_kind) ≤ (1 : Int)) ((r1_mode) ≤ (0 : Int)) ((r1_mode) ≤ (-1 : Int)) ((r1_level) ≤ (0 : Int)) ((r1_level) ≤ (-1 : Int)) ((r1_group) ≤ (0 : Int)) ((r1_group) ≤ (-1 : Int)) ((r1_depth) ≤ (0 : Int)) ((r1_depth) ≤ (-1 : Int)) ((r1_node) ≤ (0 : Int)) ((r1_node) ≤ (-1 : Int)) ((r1_sign) ≤ (0 : Int)) ((r1_sign) ≤ (-1 : Int)) ((r1_kind) ≤ (0 : Int)) ((r1_kind) ≤ (-1 : Int)) ((r1_mode) ≤ (5 : Int)) ((h + ((-1 : Int) * r1_level)) ≤ (-1 : Int)) ((r1_group) ≤ (1 : Int)) ((r1_group) ≤ (2 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (-1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) ((r1_sign) ≤ (2 : Int)) ((r1_sign) ≤ (1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_2864 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) hn

-- Checked replay of mp.
theorem replay_2073 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : (formula_774 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact Iff.mp (replay_2072 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (replay_2071 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146)

theorem propositional_717 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p4))))) ∨ (¬ ((((¬ p13) ∨ (¬ p10)) ∧ ((¬ ((¬ p14) ∨ (¬ p15))) ∨ (¬ ((¬ p16) ∨ (¬ p17))))) ∨ ((¬ ((¬ p13) ∨ (¬ p10))) ∧ (¬ ((¬ p18) ∨ (¬ p19))))))) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2074 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_773 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_mode ≥ (0 : Int))) := by
  exact (propositional_717 (r1_group ≤ (0 : Int)) (r1_group ≥ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_level ≥ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_level ≤ (0 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_node ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2075 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i147 : (¬ (r1_mode ≥ (0 : Int)))) : (formula_773 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (Or.elim (replay_2074 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i147 t0))))

theorem propositional_718 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14) ∨ (¬ p15)) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2076 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_mode ≥ (0 : Int))) := by
  exact (propositional_718 (r1_mode ≥ (6 : Int)) (r1_sign ≥ (0 : Int)) (r1_kind ≤ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_node ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (r1_group ≤ (2 : Int)) (r1_group ≥ (2 : Int)) (r1_level ≥ (1 : Int)) ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2077 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i147 : (¬ (r1_mode ≥ (0 : Int)))) : (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (Or.elim (replay_2076 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i147 t0))))

theorem propositional_719 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2078 (r1_kind : Int) : ((¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) ∨ (¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))) := by
  exact (propositional_719 (r1_kind ≤ (2 : Int)) (r1_kind ≥ (2 : Int)))

theorem propositional_720 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p12) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2079 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_kind ≤ (2 : Int))) := by
  exact (propositional_720 (r1_sign ≥ (0 : Int)) (r1_group ≤ (0 : Int)) (r1_group ≥ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_node ≤ (0 : Int)) (r1_level ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (2 : Int)) (r1_level ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2080 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i148 : (¬ (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))) : (r1_kind ≤ (2 : Int)) := by
  exact (Or.elim (replay_2079 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (False.elim (i148 l0))) (fun t0 => t0))

theorem propositional_721 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p11) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2081 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_kind ≥ (2 : Int))) := by
  exact (propositional_721 (r1_sign ≥ (0 : Int)) (r1_group ≤ (0 : Int)) (r1_group ≥ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_node ≤ (0 : Int)) (r1_level ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (2 : Int)) (r1_level ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2082 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i148 : (¬ (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))) : (r1_kind ≥ (2 : Int)) := by
  exact (Or.elim (replay_2081 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (False.elim (i148 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2083 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i148 : (¬ (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))) (i149 : ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int))))) : False := by
  exact (Or.elim (replay_2078 r1_kind) (fun l0 => (False.elim (l0 i149))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_2080 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i148)))) (fun t1 => (False.elim (t1 (replay_2082 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i148)))))))

-- Checked replay of lemma.
theorem replay_2084 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (¬ ((¬ (r1_kind ≤ (2 : Int))) ∨ (¬ (r1_kind ≥ (2 : Int)))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_2083 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

-- Checked replay of unit-resolution.
theorem replay_2085 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (Or.elim (replay_2084 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (t0 (replay_1109 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62)))))

-- Checked replay of unit-resolution.
theorem replay_2086 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i147 : (¬ (r1_mode ≥ (0 : Int)))) : False := by
  exact (Or.elim (replay_2073 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146) (fun l0 => (False.elim (l0 (replay_2085 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i62)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_2077 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i147)))) (fun t1 => (False.elim (t1 (replay_2075 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i147)))))))

-- Checked replay of lemma.
theorem replay_2087 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) : (r1_mode ≥ (0 : Int)) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_2086 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i146 i62 (fun q => nc q))

abbrev shared_expr_Repair033_31 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) : Prop := (((r2_depth + ((-1 : Int) * c0_level)) ≤ (-1 : Int)) ∨ (¬ (formula_77 c0_group c0_level c0_mode r2_depth r2_kind r2_node r2_sign)) ∨ (¬ (formula_578 c0_group c0_level c0_mode r1_depth r1_kind r1_node r1_sign)) ∨ (¬ ((¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (formula_721 c0_group c0_level r3_depth r3_kind r3_sign)))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c0_level)) ≤ (0 : Int))) ∨ (¬ (r1_kind ≤ (1 : Int))) ∨ (¬ (r1_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c2_level)) ≥ (0 : Int))) ∨ (¬ (formula_687 c2_group c2_level c2_mode r3_depth r3_kind r3_node r3_sign)) ∨ (¬ ((¬ (c2_mode ≤ (0 : Int))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_700 c2_group c2_level r1_depth r1_kind r1_sign)))) ∨ (¬ (c2_mode ≥ (0 : Int))) ∨ (¬ (formula_194 c2_group c2_level c2_mode r2_depth r2_kind r2_node r2_sign)) ∨ (r1_mode ≥ (4 : Int)) ∨ (¬ ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int))) ∨ (¬ (formula_638 h r1_depth r1_sign)) ∨ (¬ ((¬ (c2_mode ≤ (1 : Int))) ∨ (¬ (c2_mode ≥ (1 : Int))) ∨ (¬ (formula_584 c2_group c2_level r1_depth r1_kind r1_sign)))) ∨ (formula_634 c0_group c0_level c0_mode c2_group c2_level c2_mode) ∨ (¬ (c2_mode ≤ (5 : Int))) ∨ (¬ ((¬ (c2_mode ≤ (5 : Int))) ∨ (¬ (c2_mode ≥ (5 : Int))) ∨ (¬ (formula_733 c2_group c2_level r1_depth r1_kind r1_node r1_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (2 : Int))) ∨ (¬ (c0_mode ≥ (2 : Int))) ∨ (¬ (formula_713 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (4 : Int))) ∨ (¬ (c0_mode ≥ (4 : Int))) ∨ (¬ (formula_710 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ (c0_mode ≤ (5 : Int))) ∨ (¬ ((¬ (c0_mode ≤ (5 : Int))) ∨ (¬ (c0_mode ≥ (5 : Int))) ∨ (¬ (formula_745 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ (c0_mode ≤ (3 : Int))) ∨ (¬ (c0_mode ≥ (3 : Int))) ∨ (¬ (formula_737 c0_group c0_level r3_depth r3_kind r3_node r3_sign)))) ∨ (¬ ((¬ ((¬ (c2_group ≤ (1 : Int))) ∨ (¬ (c2_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c2_group ≤ (2 : Int))) ∨ (¬ (c2_group ≥ (2 : Int))))))) ∨ (¬ ((h + ((-1 : Int) * c1_level)) ≥ (0 : Int))) ∨ (formula_696 c0_group c0_level c0_mode c1_group c1_level c1_mode) ∨ (¬ ((¬ (c0_mode ≤ (1 : Int))) ∨ (¬ (c0_mode ≥ (1 : Int))) ∨ (¬ (formula_694 c0_group c0_level r3_depth r3_kind r3_sign)))) ∨ (¬ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_group ≤ (2 : Int))) ∨ (¬ (c0_group ≥ (2 : Int))))))) ∨ (c0_level ≤ (0 : Int)))
abbrev formula_775 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign : Int) : Prop := (shared_expr_Repair033_31 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign)

-- Checked replay of unit-resolution.
theorem replay_2088 (c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i10 : (formula_164 h r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i93 : (formula_664 h r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) (i62 : (formula_606 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign)) (i23 : (formula_312 r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign)) : (formula_775 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_kind r1_mode r1_node r1_sign r2_depth r2_kind r2_node r2_sign r3_depth r3_kind r3_node r3_sign) := by
  exact (Or.elim (replay_2061 c0_group c0_level c0_mode c1_group c1_level c1_mode c2_group c2_level c2_mode h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign r3_depth r3_group r3_kind r3_level r3_mode r3_node r3_sign i10 i93 i62 i23) (fun l0 => (Or.inl l0)) (fun t0 => (Or.elim t0 (fun l1 => (Or.inr (Or.inl l1))) (fun t1 => (Or.elim t1 (fun l2 => (Or.inr (Or.inr (Or.inl l2)))) (fun t2 => (Or.elim t2 (fun l3 => (Or.inr (Or.inr (Or.inr (Or.inl l3))))) (fun t3 => (Or.elim t3 (fun l4 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l4)))))) (fun t4 => (Or.elim t4 (fun l5 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l5))))))) (fun t5 => (Or.elim t5 (fun l6 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l6)))))))) (fun t6 => (Or.elim t6 (fun l7 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l7))))))))) (fun t7 => (Or.elim t7 (fun l8 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l8)))))))))) (fun t8 => (Or.elim t8 (fun l9 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l9))))))))))) (fun t9 => (Or.elim t9 (fun l10 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l10)))))))))))) (fun t10 => (Or.elim t10 (fun l11 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l11))))))))))))) (fun t11 => (Or.elim t11 (fun l12 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l12)))))))))))))) (fun t12 => (Or.elim t12 (fun l13 => (False.elim (l13 (replay_2087 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign r2_depth r2_group r2_kind r2_level r2_mode r2_node r2_sign i146 i62)))) (fun t13 => (Or.elim t13 (fun l14 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l14))))))))))))))) (fun t14 => (Or.elim t14 (fun l15 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l15)))))))))))))))) (fun t15 => (Or.elim t15 (fun l16 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l16))))))))))))))))) (fun t16 => (Or.elim t16 (fun l17 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l17)))))))))))))))))) (fun t17 => (Or.elim t17 (fun l18 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l18))))))))))))))))))) (fun t18 => (Or.elim t18 (fun l19 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l19)))))))))))))))))))) (fun t19 => (Or.elim t19 (fun l20 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l20))))))))))))))))))))) (fun t20 => (Or.elim t20 (fun l21 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l21)))))))))))))))))))))) (fun t21 => (Or.elim t21 (fun l22 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l22))))))))))))))))))))))) (fun t22 => (Or.elim t22 (fun l23 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l23)))))))))))))))))))))))) (fun t23 => (Or.elim t23 (fun l24 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l24))))))))))))))))))))))))) (fun t24 => (Or.elim t24 (fun l25 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l25)))))))))))))))))))))))))) (fun t25 => (Or.elim t25 (fun l26 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l26))))))))))))))))))))))))))) (fun t26 => (Or.elim t26 (fun l27 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l27)))))))))))))))))))))))))))) (fun t27 => (Or.elim t27 (fun l28 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l28))))))))))))))))))))))))))))) (fun t28 => (Or.elim t28 (fun l29 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l29)))))))))))))))))))))))))))))) (fun t29 => (Or.elim t29 (fun l30 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l30))))))))))))))))))))))))))))))) (fun t30 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t30))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- Checked replay of th-lemma.
theorem replay_2089 (r1_mode : Int) : ((r1_mode ≥ (3 : Int)) ∨ (¬ (r1_mode ≥ (4 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_2090 (r1_mode : Int) : ((r1_mode ≥ (2 : Int)) ∨ (¬ (r1_mode ≥ (3 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_2091 (r1_mode : Int) : ((r1_mode ≥ (1 : Int)) ∨ (¬ (r1_mode ≥ (2 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of th-lemma.
theorem replay_2092 (r1_mode : Int) : ((¬ (r1_mode ≤ (0 : Int))) ∨ (¬ (r1_mode ≥ (1 : Int)))) := by
  classical
  first | omega | grind (splits := 40)

theorem propositional_722 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ ((¬ p11) ∨ (¬ p6) ∨ (¬ ((¬ p12) ∨ (¬ p4))))) ∨ (¬ ((((¬ p13) ∨ (¬ p10)) ∧ ((¬ ((¬ p14) ∨ (¬ p15))) ∨ (¬ ((¬ p16) ∨ (¬ p17))))) ∨ ((¬ ((¬ p13) ∨ (¬ p10))) ∧ (¬ ((¬ p18) ∨ (¬ p19))))))) ∨ p3) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2093 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_773 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_mode ≤ (0 : Int))) := by
  exact (propositional_722 (r1_group ≤ (0 : Int)) (r1_group ≥ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_level ≥ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_level ≤ (0 : Int)) (r1_kind ≤ (1 : Int)) (r1_kind ≥ (1 : Int)) ((h + ((-1 : Int) * r1_depth)) ≥ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_node ≤ (0 : Int)) ((h + ((-1 : Int) * r1_depth)) ≤ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_sign ≥ (0 : Int)) (r1_sign ≤ (1 : Int)) (r1_sign ≥ (1 : Int)) (r1_sign ≤ (2 : Int)) (r1_sign ≥ (2 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2094 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i150 : (¬ (r1_mode ≤ (0 : Int)))) : (formula_773 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (Or.elim (replay_2093 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i150 t0))))

theorem propositional_723 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p4) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2095 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_mode ≤ (0 : Int))) := by
  exact (propositional_723 (r1_sign ≥ (0 : Int)) (r1_group ≤ (0 : Int)) (r1_group ≥ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_mode ≤ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_node ≤ (0 : Int)) (r1_level ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_kind ≥ (2 : Int)) (r1_kind ≤ (2 : Int)) (r1_level ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2096 (r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i150 : (¬ (r1_mode ≤ (0 : Int)))) : (formula_771 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (Or.elim (replay_2095 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.elim t111 (fun l112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l112)))))))))))))) (fun t112 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t112)))))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (i150 t0))))

-- Checked replay of unit-resolution.
theorem replay_2097 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i150 : (¬ (r1_mode ≤ (0 : Int)))) (i151 : (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : False := by
  exact (Or.elim (replay_2073 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146) (fun l0 => (False.elim (l0 (replay_2096 r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i150)))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i151))) (fun t1 => (False.elim (t1 (replay_2094 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i150)))))))

-- Checked replay of lemma.
theorem replay_2098 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) : ((r1_mode ≤ (0 : Int)) ∨ (¬ (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_2097 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146 (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr q))))

theorem propositional_724 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2099 (r1_kind : Int) : ((¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) ∨ (¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))) := by
  exact (propositional_724 (r1_kind ≤ (0 : Int)) (r1_kind ≥ (0 : Int)))

theorem propositional_725 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14) ∨ (¬ p15)) ∨ p6) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2100 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_kind ≥ (0 : Int))) := by
  exact (propositional_725 (r1_mode ≥ (6 : Int)) (r1_sign ≥ (0 : Int)) (r1_kind ≤ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_node ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (r1_group ≤ (2 : Int)) (r1_group ≥ (2 : Int)) (r1_level ≥ (1 : Int)) ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2101 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i152 : (¬ (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))) : (r1_kind ≥ (0 : Int)) := by
  exact (Or.elim (replay_2100 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (False.elim (i152 l0))) (fun t0 => t0))

theorem propositional_726 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ ((¬ ((¬ p10) ∨ (¬ p11))) ∨ (¬ ((¬ p12) ∨ (¬ p13))))) ∨ (¬ p14) ∨ (¬ p15)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2102 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (r1_kind ≤ (0 : Int))) := by
  exact (propositional_726 (r1_mode ≥ (6 : Int)) (r1_sign ≥ (0 : Int)) (r1_kind ≤ (0 : Int)) (r1_mode ≥ (0 : Int)) (r1_node ≥ (0 : Int)) (r1_node ≤ (0 : Int)) (r1_kind ≥ (0 : Int)) (r1_sign ≤ (0 : Int)) (r1_depth ≤ (0 : Int)) (r1_depth ≥ (0 : Int)) (r1_group ≤ (1 : Int)) (r1_group ≥ (1 : Int)) (r1_group ≤ (2 : Int)) (r1_group ≥ (2 : Int)) (r1_level ≥ (1 : Int)) ((h + ((-1 : Int) * r1_level)) ≥ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_2103 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i152 : (¬ (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))) : (r1_kind ≤ (0 : Int)) := by
  exact (Or.elim (replay_2102 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (False.elim (i152 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2104 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i153 : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) (i152 : (¬ (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign))) : False := by
  exact (Or.elim (replay_2099 r1_kind) (fun l0 => (False.elim (l0 i153))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_2103 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i152)))) (fun t1 => (False.elim (t1 (replay_2101 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i152)))))))

-- Checked replay of lemma.
theorem replay_2105 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) : ((formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) ∨ (¬ ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int)))))) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_2104 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign (Classical.byContradiction (fun q => nc (Or.inr q))) (fun q => nc (Or.inl q)))

-- Checked replay of unit-resolution.
theorem replay_2106 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i153 : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) : (formula_772 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) := by
  exact (Or.elim (replay_2105 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.elim t100 (fun l101 => (Or.inr (Or.inl l101))) (fun t101 => (Or.elim t101 (fun l102 => (Or.inr (Or.inr (Or.inl l102)))) (fun t102 => (Or.elim t102 (fun l103 => (Or.inr (Or.inr (Or.inr (Or.inl l103))))) (fun t103 => (Or.elim t103 (fun l104 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l104)))))) (fun t104 => (Or.elim t104 (fun l105 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l105))))))) (fun t105 => (Or.elim t105 (fun l106 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l106)))))))) (fun t106 => (Or.elim t106 (fun l107 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l107))))))))) (fun t107 => (Or.elim t107 (fun l108 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l108)))))))))) (fun t108 => (Or.elim t108 (fun l109 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l109))))))))))) (fun t109 => (Or.elim t109 (fun l110 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l110)))))))))))) (fun t110 => (Or.elim t110 (fun l111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl l111))))))))))))) (fun t111 => (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr t111))))))))))))))))))))))))))))))))))))) (fun t0 => (False.elim (t0 i153))))

-- Checked replay of unit-resolution.
theorem replay_2107 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i153 : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) : (r1_mode ≤ (0 : Int)) := by
  exact (Or.elim (replay_2098 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146) (fun l0 => l0) (fun t0 => (False.elim (t0 (replay_2106 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i153)))))

-- Checked replay of unit-resolution.
theorem replay_2108 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i153 : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) : (¬ (r1_mode ≥ (1 : Int))) := by
  exact (Or.elim (replay_2092 r1_mode) (fun l0 => (False.elim (l0 (replay_2107 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146 i153)))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2109 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i153 : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) : (¬ (r1_mode ≥ (2 : Int))) := by
  exact (Or.elim (replay_2091 r1_mode) (fun l0 => (False.elim ((replay_2108 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146 i153) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2110 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i153 : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) : (¬ (r1_mode ≥ (3 : Int))) := by
  exact (Or.elim (replay_2090 r1_mode) (fun l0 => (False.elim ((replay_2109 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146 i153) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_2111 (h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign : Int) (i146 : (formula_765 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign)) (i153 : ((¬ (r1_kind ≤ (0 : Int))) ∨ (¬ (r1_kind ≥ (0 : Int))))) : (¬ (r1_mode ≥ (4 : Int))) := by
  exact (Or.elim (replay_2089 r1_mode) (fun l0 => (False.elim ((replay_2110 h r1_depth r1_group r1_kind r1_level r1_mode r1_node r1_sign i146 i153) l0))) (fun t0 => t0))

abbrev shared_expr_Repair033_32 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((c0_mode ≥ (6 : Int)) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (c0_depth ≤ (0 : Int))) ∨ (¬ (c0_depth ≥ (0 : Int))) ∨ (¬ (c0_node ≤ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))) ∨ (¬ (c0_kind ≤ (0 : Int))) ∨ (¬ (c0_kind ≥ (0 : Int))) ∨ (¬ (c0_level ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int))) ∨ (¬ ((¬ ((¬ (c0_group ≤ (1 : Int))) ∨ (¬ (c0_group ≥ (1 : Int))))) ∨ (¬ ((¬ (c0_group ≤ (2 : Int))) ∨ (¬ (c0_group ≥ (2 : Int))))))))
abbrev formula_776 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair033_32 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

theorem propositional_727 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Prop) : ((p0 ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ ((¬ ((¬ p12) ∨ (¬ p13))) ∨ (¬ ((¬ p14) ∨ (¬ p15)))))) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2112 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_776 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ∨ (c0_mode ≥ (0 : Int))) := by
  exact (propositional_727 (c0_mode ≥ (6 : Int)) (c0_mode ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≤ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)) (c0_kind ≤ (0 : Int)) (c0_kind ≥ (0 : Int)) (c0_level ≥ (1 : Int)) ((h + ((-1 : Int) * c0_level)) ≥ (0 : Int)) (c0_group ≤ (1 : Int)) (c0_group ≥ (1 : Int)) (c0_group ≤ (2 : Int)) (c0_group ≥ (2 : Int)))

abbrev shared_expr_Repair033_33 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : Prop := ((¬ (c0_kind ≤ (2 : Int))) ∨ (¬ (c0_kind ≥ (2 : Int))) ∨ (¬ (c0_mode ≤ (0 : Int))) ∨ (¬ (c0_mode ≥ (0 : Int))) ∨ (¬ (c0_level ≤ (0 : Int))) ∨ (¬ (c0_level ≥ (0 : Int))) ∨ (¬ (c0_group ≤ (0 : Int))) ∨ (¬ (c0_group ≥ (0 : Int))) ∨ (¬ (c0_depth ≤ (0 : Int))) ∨ (¬ (c0_depth ≥ (0 : Int))) ∨ (¬ (c0_node ≤ (0 : Int))) ∨ (¬ (c0_node ≥ (0 : Int))) ∨ (¬ (c0_sign ≤ (0 : Int))) ∨ (¬ (c0_sign ≥ (0 : Int))))
abbrev formula_777 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : Prop := (shared_expr_Repair033_33 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign)

theorem propositional_728 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p13)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_2113 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign : Int) : ((formula_777 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign) ∨ (c0_kind ≥ (2 : Int))) := by
  exact (propositional_728 (c0_kind ≤ (2 : Int)) (c0_kind ≥ (2 : Int)) (c0_mode ≤ (0 : Int)) (c0_mode ≥ (0 : Int)) (c0_level ≤ (0 : Int)) (c0_level ≥ (0 : Int)) (c0_group ≤ (0 : Int)) (c0_group ≥ (0 : Int)) (c0_depth ≤ (0 : Int)) (c0_depth ≥ (0 : Int)) (c0_node ≤ (0 : Int)) (c0_node ≥ (0 : Int)) (c0_sign ≤ (0 : Int)) (c0_sign ≥ (0 : Int)))

abbrev shared_expr_Repair033_34 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((c0_kind = (0 : Int)) ∧ (c0_mode ≥ (0 : Int)) ∧ (c0_mode < (6 : Int)) ∧ (c0_level ≥ (1 : Int)) ∧ (c0_level ≤ h) ∧ ((c0_group = (1 : Int)) ∨ (c0_group = (2 : Int))) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int)))
abbrev formula_778 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair033_34 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

abbrev shared_expr_Repair033_35 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((c0_kind = (0 : Int)) ∧ (c0_mode ≥ (0 : Int)) ∧ (¬ ((6 : Int) ≤ c0_mode)) ∧ (c0_level ≥ (1 : Int)) ∧ (c0_level ≤ h) ∧ ((c0_group = (1 : Int)) ∨ (c0_group = (2 : Int))) ∧ (c0_depth = (0 : Int)) ∧ (c0_node = (0 : Int)) ∧ (c0_sign = (0 : Int)))
abbrev formula_779 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := (shared_expr_Repair033_35 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)

theorem normalized_729 (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Prop) : ((p0 ∧ (¬ p1) ∧ p2 ∧ (¬ p3) ∧ p4 ∧ p5 ∧ p6 ∧ p7 ∧ p8) ↔ (p0 ∧ (¬ p1) ∧ (¬ (¬ p2)) ∧ (¬ p3) ∧ p4 ∧ p5 ∧ p6 ∧ p7 ∧ p8)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_2865 (c0_mode : Int) : (c0_mode < (6 : Int)) ↔ ((c0_mode) ≤ (5 : Int)) := by
  omega

theorem normalization_2866 (c0_level : Int) : (c0_level ≥ (1 : Int)) ↔ (¬ ((c0_level) ≤ (0 : Int))) := by
  omega

theorem normalization_2867 (c0_level h : Int) : (c0_level ≤ h) ↔ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) := by
  omega

theorem normalization_2868 (c0_group : Int) : (c0_group = (2 : Int)) ↔ (((c0_group) ≤ (2 : Int)) ∧ (¬ ((c0_group) ≤ (1 : Int)))) := by
  omega

theorem normalization_2869 (c0_group : Int) : ((c0_group = (1 : Int)) ∨ (c0_group = (2 : Int))) ↔ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∨ (((c0_group) ≤ (2 : Int)) ∧ (¬ ((c0_group) ≤ (1 : Int))))) := (or_congr (normalization_180 c0_group) (normalization_2868 c0_group))

theorem normalization_2870 (c0_depth : Int) : (c0_depth = (0 : Int)) ↔ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) := by
  omega

theorem normalization_2871 (c0_node : Int) : (c0_node = (0 : Int)) ↔ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) := by
  omega

abbrev shared_expr_Repair033_36 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (¬ ((c0_mode) ≤ (-1 : Int))) ∧ ((c0_mode) ≤ (5 : Int)) ∧ (¬ ((c0_level) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∨ (((c0_group) ≤ (2 : Int)) ∧ (¬ ((c0_group) ≤ (1 : Int))))) ∧ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) ∧ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
theorem normalization_2872 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_778 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair033_36 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (and_congr (normalization_134 c0_kind) (and_congr (normalization_628 c0_mode) (and_congr (normalization_2865 c0_mode) (and_congr (normalization_2866 c0_level) (and_congr (normalization_2867 c0_level h) (and_congr (normalization_2869 c0_group) (and_congr (normalization_2870 c0_depth) (and_congr (normalization_2871 c0_node) (normalization_144 c0_sign)))))))))

theorem normalization_2873 (c0_mode : Int) : ((6 : Int) ≤ c0_mode) ↔ (¬ ((c0_mode) ≤ (5 : Int))) := by
  omega

theorem normalization_2874 (c0_mode : Int) : (¬ ((6 : Int) ≤ c0_mode)) ↔ (¬ (¬ ((c0_mode) ≤ (5 : Int)))) := (not_congr (normalization_2873 c0_mode))

abbrev shared_expr_Repair033_37 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : Prop := ((((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ∧ (¬ ((c0_mode) ≤ (-1 : Int))) ∧ (¬ (¬ ((c0_mode) ≤ (5 : Int)))) ∧ (¬ ((c0_level) ≤ (0 : Int))) ∧ ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ∧ ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∨ (((c0_group) ≤ (2 : Int)) ∧ (¬ ((c0_group) ≤ (1 : Int))))) ∧ (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) ∧ (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) ∧ (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
theorem normalization_2875 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : (formula_779 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair033_37 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) := (and_congr (normalization_134 c0_kind) (and_congr (normalization_628 c0_mode) (and_congr (normalization_2874 c0_mode) (and_congr (normalization_2866 c0_level) (and_congr (normalization_2867 c0_level h) (and_congr (normalization_2869 c0_group) (and_congr (normalization_2870 c0_depth) (and_congr (normalization_2871 c0_node) (normalization_144 c0_sign)))))))))

theorem normalization_2876 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_778 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_779 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) ↔ ((shared_expr_Repair033_36 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (shared_expr_Repair033_37 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := (iff_congr (normalization_2872 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) (normalization_2875 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h))

-- Checked replay of rewrite.
theorem replay_2114 (c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h : Int) : ((formula_778 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) ↔ (formula_779 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h)) := by
  classical
  have ht := (normalized_729 (((c0_kind) ≤ (0 : Int)) ∧ (¬ ((c0_kind) ≤ (-1 : Int)))) ((c0_mode) ≤ (-1 : Int)) ((c0_mode) ≤ (5 : Int)) ((c0_level) ≤ (0 : Int)) ((c0_level + ((-1 : Int) * h)) ≤ (0 : Int)) ((((c0_group) ≤ (1 : Int)) ∧ (¬ ((c0_group) ≤ (0 : Int)))) ∨ (((c0_group) ≤ (2 : Int)) ∧ (¬ ((c0_group) ≤ (1 : Int))))) (((c0_depth) ≤ (0 : Int)) ∧ (¬ ((c0_depth) ≤ (-1 : Int)))) (((c0_node) ≤ (0 : Int)) ∧ (¬ ((c0_node) ≤ (-1 : Int)))) (((c0_sign) ≤ (0 : Int)) ∧ (¬ ((c0_sign) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_2876 c0_depth c0_group c0_kind c0_level c0_mode c0_node c0_sign h) hn

end H4Formal.Generated.Repair
