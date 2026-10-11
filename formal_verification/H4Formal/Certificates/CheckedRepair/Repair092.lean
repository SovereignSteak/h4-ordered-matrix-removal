import H4Formal.BooleanReplaySupport
import H4Formal.Certificates.CheckedRepair.Repair091

namespace H4Formal.Generated.Repair

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem propositional_1985 (p0 p1 : Prop) : (((¬ p0) ∨ (¬ p1)) ∨ p1) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6076 (c3_sign : Int) : (((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) ∨ (c3_sign ≥ (1 : Int))) := by
  exact (propositional_1985 (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6077 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int)))) := by
  exact (Or.elim (replay_6076 c3_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_6063 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) t0))))

-- Checked replay of unit-resolution.
theorem replay_6078 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ ((¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))))) := by
  exact (Or.elim (replay_6009 c3_sign) (fun l0 => (False.elim (l0 (replay_6061 c3_depth c3_sign h i373 i375)))) (fun t0 => (Or.elim t0 (fun l1 => l1) (fun t1 => (False.elim (t1 (replay_6077 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))))))

-- Checked replay of unit-resolution.
theorem replay_6079 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (c3_sign ≥ (0 : Int)) := by
  exact (Or.elim (replay_6075 c3_sign) (fun l0 => (False.elim ((replay_6078 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6080 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) := by
  exact (Or.elim (replay_5995 c3_node c3_sign r2_node r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6062 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6079 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t2 => (Or.elim t2 (fun l3 => (False.elim (l3 i61))) (fun t3 => (False.elim (t3 (replay_6074 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))))))))))

abbrev shared_expr_Repair092_0 (c3_depth h r2_depth r3_depth : Int) : Prop := ((¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))
abbrev formula_2252 (c3_depth h r2_depth r3_depth : Int) : Prop := (shared_expr_Repair092_0 c3_depth h r2_depth r3_depth)

-- Checked replay of th-lemma.
theorem replay_6081 (c3_depth h r2_depth r3_depth : Int) : (formula_2252 c3_depth h r2_depth r3_depth) := by
  classical
  first | omega | grind (splits := 40)

-- Checked replay of unit-resolution.
theorem replay_6082 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((r3_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_6006 c3_depth c3_node c3_sign r3_depth r3_node r3_sign) (fun l0 => (False.elim ((replay_6068 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6083 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) := by
  exact (Or.elim (replay_6081 c3_depth h r2_depth r3_depth) (fun l0 => (False.elim (l0 i372))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 i364))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6082 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_6084 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : (¬ ((¬ (formula_2229 c3_node c3_sign r2_node r2_sign)) ∨ (¬ (formula_2230 c3_node c3_sign r2_node r2_sign)))) := by
  exact (Or.elim (replay_6022 c3_depth c3_node c3_sign r2_depth r2_node r2_sign) (fun l0 => (False.elim (l0 i371))) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6083 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368)))) (fun t1 => (Or.elim t1 (fun l2 => (False.elim (l2 (replay_6055 c3_depth h r2_depth i69 i373)))) (fun t2 => t2))))))

-- Checked replay of unit-resolution.
theorem replay_6085 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) (i372 : ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) (i374 : (¬ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)))) (i69 : ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) (i364 : ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) (i373 : (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) (i375 : (formula_2250 c3_depth c3_sign h)) (i61 : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i65 : ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) (i371 : (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) (i367 : ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) (i368 : (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) : False := by
  exact (Or.elim (replay_5994 c3_node c3_sign r2_node r2_sign) (fun l0 => (False.elim ((replay_6084 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i65 i371 i367 i368) l0))) (fun t0 => (False.elim ((replay_6080 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign i372 i374 i69 i364 i373 i375 i61 i65 i371 i367 i368) t0))))

abbrev shared_expr_Repair092_1 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : Prop := (((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) ∨ ((r2_node + ((-1 : Int) * r3_node)) ≥ (0 : Int)) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r3_depth)) ≤ (0 : Int))) ∨ (¬ (formula_2240 c3_depth c3_node c3_sign h r3_depth r3_node r3_sign)) ∨ (¬ ((¬ (r3_sign ≤ (0 : Int))) ∨ (¬ (r3_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r3_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ (formula_2250 c3_depth c3_sign h)) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))))
abbrev formula_2253 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : Prop := (shared_expr_Repair092_1 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign)

-- Checked replay of lemma.
theorem replay_6086 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign : Int) : (formula_2253 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign) := by
  classical
  apply Classical.byContradiction
  intro nc
  exact (replay_6085 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign r3_depth r3_node r3_sign (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))) (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))) (fun q => nc (Or.inl q)) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inl q)))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inl q))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q)))))))))) (Classical.byContradiction (fun q => nc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl q))))))))))

theorem propositional_1986 (p0 p1 p2 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p2)) ∨ p2) := by
  classical
  first | (by_cases case_p2 : p2 <;> simp [case_p2, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6087 (r2_sign : Int) : (((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ∨ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))) := by
  exact (propositional_1986 (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))

theorem propositional_1987 (p0 p1 : Prop) : ((¬ ((¬ p0) ∨ (¬ p1))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6088 (r2_sign : Int) : ((¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))) ∨ (¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))) := by
  exact (propositional_1987 (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)))

theorem propositional_1988 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((¬ p0) ∨ (¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6)) ∨ p2) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6089 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) : ((formula_0 c2_node c2_sign h r2_depth r2_node r2_sign) ∨ (r2_sign ≤ (2 : Int))) := by
  exact (propositional_1988 ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c2_sign ≤ (2 : Int)) (c2_sign ≥ (2 : Int)) ((r2_node + ((-1 : Int) * c2_node)) ≤ (0 : Int)))

-- Checked replay of unit-resolution.
theorem replay_6090 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : (r2_sign ≤ (2 : Int)) := by
  exact (Or.elim (replay_6089 c2_node c2_sign h r2_depth r2_node r2_sign) (fun l0 => (False.elim (i363 l0))) (fun t0 => t0))

-- Checked replay of unit-resolution.
theorem replay_6091 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))) := by
  exact (Or.elim (replay_6088 r2_sign) (fun l0 => l0) (fun t0 => (Or.elim t0 (fun l1 => (False.elim (l1 (replay_6090 c2_node c2_sign h r2_depth r2_node r2_sign i363)))) (fun t1 => (False.elim (t1 (replay_5952 c2_node c2_sign h r2_depth r2_node r2_sign i363)))))))

-- Checked replay of unit-resolution.
theorem replay_6092 (c2_node c2_sign h r2_depth r2_node r2_sign : Int) (i363 : (¬ (formula_0 c2_node c2_sign h r2_depth r2_node r2_sign))) : ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) := by
  exact (Or.elim (replay_6087 r2_sign) (fun l0 => (Or.elim l0 (fun l100 => (Or.inl l100)) (fun t100 => (Or.inr t100)))) (fun t0 => (False.elim ((replay_6091 c2_node c2_sign h r2_depth r2_node r2_sign i363) t0))))

abbrev shared_expr_Repair092_2 (c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int))) ∨ (¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))) ∨ (¬ (c3_sign ≤ (2 : Int))) ∨ (¬ (c3_sign ≥ (2 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))
abbrev formula_2254 (c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_2 c3_node c3_sign h r2_depth r2_node r2_sign)

abbrev shared_expr_Repair092_3 (c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := (((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ∨ ((r2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ∨ (¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))
abbrev formula_2255 (c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_3 c3_node c3_sign h r2_depth r2_node r2_sign)

abbrev shared_expr_Repair092_4 (c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (0 : Int))) ∨ (¬ (c3_sign ≥ (0 : Int))) ∨ (¬ ((r2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))))) ∨ (¬ (formula_2254 c3_node c3_sign h r2_depth r2_node r2_sign)) ∨ (¬ (formula_2255 c3_node c3_sign h r2_depth r2_node r2_sign)))
abbrev formula_2256 (c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_4 c3_node c3_sign h r2_depth r2_node r2_sign)

abbrev shared_expr_Repair092_5 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := ((¬ ((¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ (formula_2256 c3_node c3_sign h r2_depth r2_node r2_sign)))) ∨ (¬ (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)))
abbrev formula_2257 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_5 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign)

theorem propositional_1989 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 : Prop) : (((¬ ((¬ p0) ∨ (¬ p1) ∨ (¬ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ (¬ ((¬ p7) ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10) ∨ (¬ p11) ∨ (¬ p12) ∨ (¬ p6))) ∨ (¬ (p7 ∨ p13 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p16) ∨ (¬ p17))))))) ∨ (¬ p18)) ∨ p18) := by
  classical
  first | (by_cases case_p18 : p18 <;> simp [case_p18, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6093 (c3_depth c3_node c3_sign h r2_depth r2_node r2_sign : Int) : ((formula_2257 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign) ∨ (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign)) := by
  exact (propositional_1989 ((r2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) (r2_sign ≤ (0 : Int)) (r2_sign ≥ (0 : Int)) (c3_sign ≤ (0 : Int)) (c3_sign ≥ (0 : Int)) ((r2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≤ (0 : Int)) ((h + ((-1 : Int) * r2_depth)) ≥ (0 : Int)) (r2_sign ≤ (2 : Int)) (r2_sign ≥ (2 : Int)) (c3_sign ≤ (2 : Int)) (c3_sign ≥ (2 : Int)) ((r2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) (r2_sign ≤ (1 : Int)) (r2_sign ≥ (1 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) (formula_2245 c3_depth c3_node c3_sign r2_depth r2_node r2_sign))

abbrev shared_expr_Repair092_6 (c3_depth c3_kind h r2_kind : Int) : Prop := ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))) ∨ (¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int))) ∨ (¬ ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))
abbrev formula_2258 (c3_depth c3_kind h r2_kind : Int) : Prop := (shared_expr_Repair092_6 c3_depth c3_kind h r2_kind)

abbrev shared_expr_Repair092_7 (c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ∧ (formula_2258 c3_depth c3_kind h r2_kind)) ∨ ((¬ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))))) ∧ (formula_2257 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign)))
abbrev formula_2259 (c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_7 c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_8 (c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((formula_2259 c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign) ∨ ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) ∨ (¬ (formula_2257 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign)))
abbrev formula_2260 (c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_8 c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign)

theorem propositional_1990 (p0 p1 p2 p3 p4 p5 p6 p7 : Prop) : (((p0 ∧ ((¬ p1) ∨ (¬ p2) ∨ (¬ p3) ∨ (¬ p4) ∨ (¬ p5) ∨ (¬ p6))) ∨ ((¬ p0) ∧ p7)) ∨ p0 ∨ (¬ p7)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6094 (c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_2260 c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign) := by
  exact (propositional_1990 ((¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int))))) ∨ (¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int)))))) (r2_kind ≤ (2 : Int)) (r2_kind ≥ (2 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)) ((h + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((h + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) (formula_2257 c3_depth c3_node c3_sign h r2_depth r2_node r2_sign))

abbrev shared_expr_Repair092_9 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (-1 : Int))))
abbrev formula_2261 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Repair092_9 c3_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Repair092_10 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (0 : Int))))
abbrev formula_2262 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Repair092_10 c3_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Repair092_11 (c3_group c3_level r2_depth r2_kind r2_sign : Int) : Prop := ((((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int)))) ∧ (¬ (formula_2261 c3_level r2_depth r2_kind r2_sign))) ∨ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∧ (¬ (formula_2262 c3_level r2_depth r2_kind r2_sign))))
abbrev formula_2263 (c3_group c3_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Repair092_11 c3_group c3_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Repair092_12 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (0 : Int))))
abbrev formula_2264 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Repair092_12 c3_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Repair092_13 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (-1 : Int))))
abbrev formula_2265 (c3_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Repair092_13 c3_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Repair092_14 (c3_group c3_level r2_depth r2_kind r2_sign : Int) : Prop := ((((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int)))) ∧ (¬ (formula_2264 c3_level r2_depth r2_kind r2_sign))) ∨ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∧ (¬ (formula_2265 c3_level r2_depth r2_kind r2_sign))))
abbrev formula_2266 (c3_group c3_level r2_depth r2_kind r2_sign : Int) : Prop := (shared_expr_Repair092_14 c3_group c3_level r2_depth r2_kind r2_sign)

abbrev shared_expr_Repair092_15 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (0 : Int))))
abbrev formula_2267 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_15 c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_16 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∧ (¬ (formula_2267 c3_level r2_depth r2_kind r2_node r2_sign))))
abbrev formula_2268 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_16 c3_group c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_17 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (0 : Int))))
abbrev formula_2269 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_17 c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_18 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∧ (¬ (formula_2269 c3_level r2_depth r2_kind r2_node r2_sign))))
abbrev formula_2270 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_18 c3_group c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_19 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (0 : Int))))
abbrev formula_2271 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_19 c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_20 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∧ (¬ (formula_2271 c3_level r2_depth r2_kind r2_node r2_sign))))
abbrev formula_2272 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_20 c3_group c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_21 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ (r2_kind ≤ (1 : Int))) ∨ (¬ (r2_kind ≥ (1 : Int))) ∨ (¬ ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int))))))) ∨ (¬ ((r2_node % (2 : Int)) ≥ (1 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((r2_depth + ((-1 : Int) * c3_level)) ≥ (0 : Int))))
abbrev formula_2273 (c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_21 c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_22 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int)))) ∧ (¬ ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))))) ∨ ((¬ ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int))))) ∧ (¬ (formula_2273 c3_level r2_depth r2_kind r2_node r2_sign))))
abbrev formula_2274 (c3_group c3_level r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_22 c3_group c3_level r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_23 (c3_group c3_level c3_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((¬ ((¬ (c3_mode ≤ (0 : Int))) ∨ (¬ (c3_mode ≥ (0 : Int))) ∨ (¬ (formula_2263 c3_group c3_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c3_mode ≤ (1 : Int))) ∨ (¬ (c3_mode ≥ (1 : Int))) ∨ (¬ (formula_2266 c3_group c3_level r2_depth r2_kind r2_sign)))) ∨ (¬ ((¬ (c3_mode ≤ (2 : Int))) ∨ (¬ (c3_mode ≥ (2 : Int))) ∨ (¬ (formula_2268 c3_group c3_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c3_mode ≤ (3 : Int))) ∨ (¬ (c3_mode ≥ (3 : Int))) ∨ (¬ (formula_2270 c3_group c3_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c3_mode ≤ (4 : Int))) ∨ (¬ (c3_mode ≥ (4 : Int))) ∨ (¬ (formula_2272 c3_group c3_level r2_depth r2_kind r2_node r2_sign)))) ∨ (¬ ((¬ (c3_mode ≤ (5 : Int))) ∨ (¬ (c3_mode ≥ (5 : Int))) ∨ (¬ (formula_2274 c3_group c3_level r2_depth r2_kind r2_node r2_sign)))))
abbrev formula_2275 (c3_group c3_level c3_mode r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_23 c3_group c3_level c3_mode r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_24 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ∧ (formula_2259 c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign)) ∨ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∧ (formula_2275 c3_group c3_level c3_mode r2_depth r2_kind r2_node r2_sign)))
abbrev formula_2276 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_24 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign)

abbrev shared_expr_Repair092_25 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := ((formula_2276 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign) ∨ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2259 c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign)))
abbrev formula_2277 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : Prop := (shared_expr_Repair092_25 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign)

theorem propositional_1991 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ ((¬ p2) ∨ (¬ p3) ∨ (¬ ((p4 ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p8) ∨ (¬ p9)))) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p12) ∨ (¬ p13) ∨ (¬ ((p4 ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p10) ∨ (¬ p11)))) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p8) ∨ (¬ p9)))))))) ∨ (¬ ((¬ p15) ∨ (¬ p16) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p18) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p19) ∨ (¬ p20) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p7) ∨ (¬ p21) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p22) ∨ (¬ p23) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p18) ∨ (¬ p10) ∨ (¬ p11)))))))) ∨ (¬ ((¬ p24) ∨ (¬ p25) ∨ (¬ ((p4 ∧ (¬ p17)) ∨ ((¬ p4) ∧ (¬ ((¬ p5) ∨ (¬ p6) ∨ (¬ p14) ∨ (¬ p21) ∨ (¬ p10) ∨ (¬ p11))))))))))) ∨ (¬ p0) ∨ (¬ p1)) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6095 (c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign : Int) : (formula_2277 c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign h r2_depth r2_kind r2_node r2_sign) := by
  exact (propositional_1991 ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) (formula_2259 c3_depth c3_kind c3_node c3_sign h r2_depth r2_kind r2_node r2_sign) (c3_mode ≤ (0 : Int)) (c3_mode ≥ (0 : Int)) ((¬ (c3_group ≤ (1 : Int))) ∨ (¬ (c3_group ≥ (1 : Int)))) (r2_kind ≤ (1 : Int)) (r2_kind ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (0 : Int))) ∨ (¬ (r2_sign ≥ (0 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) ((r2_depth + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) ((r2_depth + ((-1 : Int) * c3_level)) ≥ (-1 : Int)) ((r2_depth + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ((r2_depth + ((-1 : Int) * c3_level)) ≥ (0 : Int)) (c3_mode ≤ (1 : Int)) (c3_mode ≥ (1 : Int)) ((¬ ((¬ (r2_sign ≤ (1 : Int))) ∨ (¬ (r2_sign ≥ (1 : Int))))) ∨ (¬ ((¬ (r2_sign ≤ (2 : Int))) ∨ (¬ (r2_sign ≥ (2 : Int)))))) (c3_mode ≤ (2 : Int)) (c3_mode ≥ (2 : Int)) ((¬ (r2_kind ≤ (2 : Int))) ∨ (¬ (r2_kind ≥ (2 : Int)))) ((r2_node % (2 : Int)) ≤ (0 : Int)) (c3_mode ≤ (3 : Int)) (c3_mode ≥ (3 : Int)) ((r2_node % (2 : Int)) ≥ (1 : Int)) (c3_mode ≤ (4 : Int)) (c3_mode ≥ (4 : Int)) (c3_mode ≤ (5 : Int)) (c3_mode ≥ (5 : Int)))

abbrev shared_expr_Repair092_26 (c2_node c3_node : Int) : Prop := (((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))))
abbrev shared_expr_Repair092_27 (c2_node c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev formula_2278 (c2_node c3_node c3_sign : Int) : Prop := ((shared_expr_Repair092_26 c2_node c3_node) ∨ (shared_expr_Repair092_27 c2_node c3_node c3_sign))

abbrev shared_expr_Repair092_28 (c2_node c3_node : Int) : Prop := (((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))
abbrev shared_expr_Repair092_29 (c2_node c2_sign c3_node : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))))))
abbrev formula_2279 (c2_node c2_sign c3_node : Int) : Prop := ((shared_expr_Repair092_28 c2_node c3_node) ∨ (shared_expr_Repair092_29 c2_node c2_sign c3_node))

abbrev shared_expr_Repair092_30 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)))) ∧ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int))) ∨ (formula_2278 c2_node c3_node c3_sign)))
abbrev shared_expr_Repair092_31 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((shared_expr_Repair092_30 c2_depth c2_node c3_depth c3_node c3_sign) ∨ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int))))) ∧ (formula_2279 c2_node c2_sign c3_node)))
abbrev formula_2280 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_31 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_32 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((¬ ((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ∧ (¬ ((¬ (c2_sign ≤ (0 : Int))) ∨ (¬ (c2_sign ≥ (0 : Int))) ∨ (¬ (c3_sign ≤ (1 : Int))) ∨ (¬ (c3_sign ≥ (1 : Int))))))
abbrev shared_expr_Repair092_33 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∨ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))) ∨ (shared_expr_Repair092_32 c2_node c2_sign c3_node c3_sign))
abbrev formula_2281 (c2_node c2_sign c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_33 c2_node c2_sign c3_node c3_sign)

abbrev shared_expr_Repair092_34 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)))) ∧ (formula_2280 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ∨ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∨ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int))))) ∧ (formula_2281 c2_node c2_sign c3_node c3_sign)))
abbrev formula_2282 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_34 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_35 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int)))) ∧ (¬ ((¬ ((¬ (c3_kind ≤ (2 : Int))) ∨ (¬ (c3_kind ≥ (2 : Int))))) ∨ (¬ (formula_2282 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))))) ∨ ((¬ ((¬ (c2_kind ≤ (2 : Int))) ∨ (¬ (c2_kind ≥ (2 : Int))))) ∧ (¬ ((¬ (c3_kind ≤ (1 : Int))) ∨ (¬ (c3_kind ≥ (1 : Int)))))))
abbrev formula_2283 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_35 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Repair092_36 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2283 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) ∨ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))
abbrev formula_2284 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_36 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

theorem propositional_1992 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 : Prop) : (((¬ p0) ∨ (¬ ((((¬ p1) ∨ (¬ p2)) ∧ (¬ ((¬ ((¬ p3) ∨ (¬ p4))) ∨ (¬ ((((¬ p5) ∨ (¬ p6)) ∧ ((((¬ p7) ∨ (¬ p8)) ∧ ((¬ p9) ∨ (¬ p10) ∨ ((((¬ p11) ∨ (¬ p12)) ∧ (¬ p11)) ∨ ((¬ ((¬ p11) ∨ (¬ p12))) ∧ (¬ ((¬ p13) ∨ (¬ p14))))))) ∨ ((¬ ((¬ p7) ∨ (¬ p8))) ∧ ((((¬ p15) ∨ (¬ p16)) ∧ (¬ p16)) ∨ ((¬ ((¬ p15) ∨ (¬ p16))) ∧ (¬ ((¬ p17) ∨ (¬ p18)))))))) ∨ ((¬ ((¬ p5) ∨ (¬ p6))) ∧ ((((¬ p19) ∨ (¬ p20)) ∧ (¬ p20)) ∨ ((¬ ((¬ p19) ∨ (¬ p20))) ∧ (¬ ((¬ p17) ∨ (¬ p18) ∨ (¬ p13) ∨ (¬ p14))))))))))) ∨ ((¬ ((¬ p1) ∨ (¬ p2))) ∧ (¬ ((¬ p21) ∨ (¬ p22))))))) ∨ p0) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6096 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2284 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := by
  exact (propositional_1992 ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) (c2_kind ≤ (2 : Int)) (c2_kind ≥ (2 : Int)) (c3_kind ≤ (2 : Int)) (c3_kind ≥ (2 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (-1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≥ (1 : Int)) ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≥ (0 : Int)) (c3_sign ≤ (1 : Int)) (c3_sign ≥ (1 : Int)) ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)) (c2_sign ≤ (0 : Int)) (c2_sign ≥ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) (c3_kind ≤ (1 : Int)) (c3_kind ≥ (1 : Int)))

abbrev shared_expr_Repair092_37 (c2_group c2_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ∧ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))))
abbrev formula_2285 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (shared_expr_Repair092_37 c2_group c2_mode c3_group c3_mode)

abbrev shared_expr_Repair092_38 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ∨ ((¬ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))))) ∧ (formula_2285 c2_group c2_mode c3_group c3_mode)))
abbrev formula_2286 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (shared_expr_Repair092_38 c2_group c2_level c2_mode c3_group c3_level c3_mode)

abbrev shared_expr_Repair092_39 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2286 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))
abbrev formula_2287 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))) ∨ (shared_expr_Repair092_39 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Repair092_40 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ∧ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2283 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev shared_expr_Repair092_41 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Repair092_40 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ∨ ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∧ (formula_2287 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)))
abbrev formula_2288 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_41 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Repair092_42 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((¬ ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int))))) ∨ (¬ ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2283 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))) ∨ (¬ (formula_2288 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)))
abbrev formula_2289 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_42 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem propositional_1993 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop) : ((¬ p0) ∨ (¬ p1) ∨ (¬ ((p0 ∧ (¬ p1)) ∨ ((¬ p0) ∧ ((¬ p2) ∨ (¬ p3) ∨ (((p4 ↔ p5) ∧ ((((¬ p6) ∨ (¬ p7)) ∧ (¬ p7)) ∨ ((¬ ((¬ p6) ∨ (¬ p7))) ∧ ((((¬ p8) ∨ (¬ p9)) ∧ (¬ p9)) ∨ ((¬ ((¬ p8) ∨ (¬ p9))) ∧ (¬ p10)))))) ∨ ((¬ (p4 ↔ p5)) ∧ p4))))))) := by
  classical
  first | (by_cases case_p0 : p0 <;> simp [case_p0, Decidable.or_not_self, Decidable.not_or_self]; done) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

-- Checked replay of def-axiom.
theorem replay_6097 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2289 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact (propositional_1993 ((¬ (c2_kind ≤ (0 : Int))) ∨ (¬ (c2_kind ≥ (0 : Int)))) ((¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ∨ (¬ (formula_2283 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) (c3_kind ≤ (0 : Int)) (c3_kind ≥ (0 : Int)) (c2_mode ≥ (4 : Int)) (c3_mode ≥ (4 : Int)) ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))

abbrev shared_expr_Repair092_43 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((¬ (¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))))) ∧ (((c2_level ≠ c3_level) ∧ (c2_level < c3_level)) ∨ ((¬ (c2_level ≠ c3_level)) ∧ (((c2_mode ≠ c3_mode) ∧ (c2_mode < c3_mode)) ∨ ((¬ (c2_mode ≠ c3_mode)) ∧ (c2_group < c3_group))))))
abbrev formula_2290 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))) ∨ (shared_expr_Repair092_43 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Repair092_44 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((((c3_depth + (1 : Int)) = c2_depth) ∧ (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ ((c2_node / (2 : Int)) < c3_node)))) ∨ ((¬ ((c3_depth + (1 : Int)) = c2_depth)) ∧ True))
abbrev formula_2291 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_44 c2_depth c2_node c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_45 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((((c2_depth + (1 : Int)) = c3_depth) ∧ (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (c2_node < (c3_node / (2 : Int)))))) ∨ ((¬ ((c2_depth + (1 : Int)) = c3_depth)) ∧ (formula_2291 c2_depth c2_node c3_depth c3_node c3_sign)))
abbrev formula_2292 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_45 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_46 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = c3_depth) ∧ (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (c2_node < c3_node)))) ∨ ((¬ (c2_depth = c3_depth)) ∧ (formula_2292 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2293 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_46 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_47 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((c2_kind = (2 : Int)) ∧ (True ∧ (c3_kind = (1 : Int)))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ (((c3_kind = (2 : Int)) ∧ False) ∨ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2293 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2294 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_47 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Repair092_48 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ (((c3_kind = (0 : Int)) ∧ (formula_2290 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ (c3_kind = (0 : Int))) ∧ True))) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (((c3_kind = (0 : Int)) ∧ False) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2294 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))))
abbrev formula_2295 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_48 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Repair092_49 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (((c2_level = c3_level) ∧ (((c2_mode = c3_mode) ∧ (¬ (c3_group ≤ c2_group))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ (c3_mode ≤ c2_mode))))) ∨ ((¬ (c2_level = c3_level)) ∧ (¬ (c3_level ≤ c2_level)))))
abbrev formula_2296 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((shared_expr_Repair092_49 c2_group c2_level c2_mode c3_group c3_level c3_mode) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))

abbrev shared_expr_Repair092_50 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (c2_depth = ((-1 : Int) + c3_depth))) ∧ ((¬ (c3_depth = ((-1 : Int) + c2_depth))) ∨ (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ (¬ (c3_node ≤ (c2_node / (2 : Int))))))))
abbrev shared_expr_Repair092_51 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = ((-1 : Int) + c3_depth)) ∧ (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (¬ ((c3_node / (2 : Int)) ≤ c2_node))))) ∨ (shared_expr_Repair092_50 c2_depth c2_node c3_depth c3_node c3_sign))
abbrev formula_2297 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_51 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_52 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = c3_depth) ∧ (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ (c3_node ≤ c2_node))))) ∨ ((¬ (c2_depth = c3_depth)) ∧ (formula_2297 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2298 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_52 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_53 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (c3_kind = (0 : Int))) ∧ (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2298 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2299 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_53 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Repair092_54 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ ((¬ (c3_kind = (0 : Int))) ∨ (formula_2296 c2_group c2_level c2_mode c3_group c3_level c3_mode))) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_2299 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev formula_2300 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_54 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Repair092_55 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2295 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2300 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2301 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_55 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1994 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 : Prop) : (((p0 ∧ ((p1 ∧ (((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2)) ∨ ((¬ (¬ ((¬ p2) ↔ (¬ p3)))) ∧ (((¬ p4) ∧ p5) ∨ ((¬ (¬ p4)) ∧ (((¬ p6) ∧ p7) ∨ ((¬ (¬ p6)) ∧ p8))))))) ∨ ((¬ p1) ∧ True))) ∨ ((¬ p0) ∧ ((p1 ∧ False) ∨ ((¬ p1) ∧ ((p9 ∧ (True ∧ p10)) ∨ ((¬ p9) ∧ ((p11 ∧ False) ∨ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ p15))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((p18 ∧ ((p19 ∧ p20) ∨ ((¬ p19) ∧ p21))) ∨ ((¬ p18) ∧ True)))))))))))))) ↔ ((p0 ∧ ((¬ p1) ∨ ((((¬ p2) ↔ (¬ p3)) ∧ ((p4 ∧ ((p6 ∧ (¬ (¬ p8))) ∨ ((¬ p6) ∧ (¬ (¬ p7))))) ∨ ((¬ p4) ∧ (¬ (¬ p5))))) ∨ ((¬ ((¬ p2) ↔ (¬ p3))) ∧ (¬ p2))))) ∨ ((¬ p0) ∧ ((¬ p1) ∧ ((p9 ∧ p10) ∨ ((¬ p9) ∧ ((¬ p11) ∧ ((p12 ∧ ((p13 ∧ p14) ∨ ((¬ p13) ∧ (¬ (¬ p15))))) ∨ ((¬ p12) ∧ ((p16 ∧ p17) ∨ ((¬ p16) ∧ ((¬ p18) ∨ ((p19 ∧ p20) ∨ ((¬ p19) ∧ (¬ (¬ p21)))))))))))))))) := by
  classical
  first | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | h4_bool_congr) | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6792 (c3_kind : Int) : (c3_kind = (0 : Int)) ↔ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) := by
  omega

theorem normalization_6793 (c3_mode : Int) : (c3_mode ≥ (4 : Int)) ↔ (¬ ((c3_mode) ≤ (3 : Int))) := by
  omega

theorem normalization_6794 (c2_mode c3_mode : Int) : (¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ↔ (¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) := (not_congr (iff_congr (normalization_1211 c2_mode) (normalization_6793 c3_mode)))

theorem normalization_6795 (c2_level c3_level : Int) : (c2_level ≠ c3_level) ↔ (¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_6796 (c2_level c3_level : Int) : (c2_level < c3_level) ↔ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6797 (c2_mode c3_mode : Int) : (c2_mode ≠ c3_mode) ↔ (¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) := by
  omega

theorem normalization_6798 (c2_mode c3_mode : Int) : (c2_mode < c3_mode) ↔ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) := by
  omega

theorem normalization_6799 (c2_group c3_group : Int) : (c2_group < c3_group) ↔ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair092_56 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (((¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))
theorem normalization_6800 (c2_group c2_mode c3_group c3_mode : Int) : (((c2_mode ≠ c3_mode) ∧ (c2_mode < c3_mode)) ∨ ((¬ (c2_mode ≠ c3_mode)) ∧ (c2_group < c3_group))) ↔ (shared_expr_Repair092_56 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_6797 c2_mode c3_mode) (normalization_6798 c2_mode c3_mode)) (and_congr (not_congr (normalization_6797 c2_mode c3_mode)) (normalization_6799 c2_group c3_group)))

abbrev shared_expr_Repair092_57 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) ∨ ((¬ (¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair092_56 c2_group c2_mode c3_group c3_mode)))
theorem normalization_6801 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (((c2_level ≠ c3_level) ∧ (c2_level < c3_level)) ∨ ((¬ (c2_level ≠ c3_level)) ∧ (((c2_mode ≠ c3_mode) ∧ (c2_mode < c3_mode)) ∨ ((¬ (c2_mode ≠ c3_mode)) ∧ (c2_group < c3_group))))) ↔ (shared_expr_Repair092_57 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6795 c2_level c3_level) (normalization_6796 c2_level c3_level)) (and_congr (not_congr (normalization_6795 c2_level c3_level)) (normalization_6800 c2_group c2_mode c3_group c3_mode)))

abbrev shared_expr_Repair092_58 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))) ∨ ((¬ (¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))))) ∧ (shared_expr_Repair092_57 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
theorem normalization_6802 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2290 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_58 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6794 c2_mode c3_mode) (normalization_1211 c2_mode)) (and_congr (not_congr (normalization_6794 c2_mode c3_mode)) (normalization_6801 c2_group c2_level c2_mode c3_group c3_level c3_mode)))

abbrev shared_expr_Repair092_59 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair092_58 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ True))
theorem normalization_6803 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (((c3_kind = (0 : Int)) ∧ (formula_2290 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ (c3_kind = (0 : Int))) ∧ True)) ↔ (shared_expr_Repair092_59 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) := (or_congr (and_congr (normalization_6792 c3_kind) (normalization_6802 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_6792 c3_kind)) (normalization_305)))

theorem normalization_6804 (c3_kind : Int) : (c3_kind = (1 : Int)) ↔ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) := by
  omega

theorem normalization_6805 (c3_kind : Int) : (True ∧ (c3_kind = (1 : Int))) ↔ (True ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) := (and_congr (normalization_305) (normalization_6804 c3_kind))

theorem normalization_6806 (c3_kind : Int) : (c3_kind = (2 : Int)) ↔ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) := by
  omega

theorem normalization_6807 (c2_depth c3_depth : Int) : (c2_depth = c3_depth) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_6808 (c2_node c3_node : Int) : (c2_node = c3_node) ↔ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_6809 (c3_sign : Int) : (c3_sign = (1 : Int)) ↔ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) := by
  omega

theorem normalization_6810 (c2_sign c3_sign : Int) : ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int))) ↔ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) := (and_congr (normalization_10 c2_sign) (normalization_6809 c3_sign))

theorem normalization_6811 (c2_node c3_node : Int) : (c2_node < c3_node) ↔ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair092_60 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ∧ ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))))
abbrev shared_expr_Repair092_61 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair092_60 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))
theorem normalization_6812 (c2_node c2_sign c3_node c3_sign : Int) : (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (c2_node < c3_node))) ↔ (shared_expr_Repair092_61 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_6808 c2_node c3_node) (normalization_6810 c2_sign c3_sign)) (and_congr (not_congr (normalization_6808 c2_node c3_node)) (normalization_6811 c2_node c3_node)))

theorem normalization_6813 (c2_depth c3_depth : Int) : ((c2_depth + (1 : Int)) = c3_depth) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_6814 (c2_node c3_node : Int) : (c2_node = (c3_node / (2 : Int))) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_6815 (c2_node c3_node : Int) : (c2_node < (c3_node / (2 : Int))) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

abbrev shared_expr_Repair092_62 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)))) ∧ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))))
abbrev shared_expr_Repair092_63 (c2_node c2_sign c3_node : Int) : Prop := ((((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) ∧ (((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int))))) ∨ (shared_expr_Repair092_62 c2_node c3_node))
theorem normalization_6816 (c2_node c2_sign c3_node : Int) : (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (c2_node < (c3_node / (2 : Int))))) ↔ (shared_expr_Repair092_63 c2_node c2_sign c3_node) := (or_congr (and_congr (normalization_6814 c2_node c3_node) (normalization_10 c2_sign)) (and_congr (not_congr (normalization_6814 c2_node c3_node)) (normalization_6815 c2_node c3_node)))

theorem normalization_6817 (c2_depth c3_depth : Int) : ((c3_depth + (1 : Int)) = c2_depth) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_6818 (c2_node c3_node : Int) : (c3_node = (c2_node / (2 : Int))) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_6819 (c2_node c3_node : Int) : ((c2_node / (2 : Int)) < c3_node) ↔ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) := by
  omega

abbrev shared_expr_Repair092_64 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
abbrev shared_expr_Repair092_65 (c2_node c3_node c3_sign : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair092_64 c2_node c3_node))
theorem normalization_6820 (c2_node c3_node c3_sign : Int) : (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ ((c2_node / (2 : Int)) < c3_node))) ↔ (shared_expr_Repair092_65 c2_node c3_node c3_sign) := (or_congr (and_congr (normalization_6818 c2_node c3_node) (normalization_6809 c3_sign)) (and_congr (not_congr (normalization_6818 c2_node c3_node)) (normalization_6819 c2_node c3_node)))

abbrev shared_expr_Repair092_66 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ∧ (shared_expr_Repair092_65 c2_node c3_node c3_sign)) ∨ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) ∧ True))
theorem normalization_6821 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : (formula_2291 c2_depth c2_node c3_depth c3_node c3_sign) ↔ (shared_expr_Repair092_66 c2_depth c2_node c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_6817 c2_depth c3_depth) (normalization_6820 c2_node c3_node c3_sign)) (and_congr (not_congr (normalization_6817 c2_depth c3_depth)) (normalization_305)))

abbrev shared_expr_Repair092_67 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair092_63 c2_node c2_sign c3_node)) ∨ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ (shared_expr_Repair092_66 c2_depth c2_node c3_depth c3_node c3_sign)))
theorem normalization_6822 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2292 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair092_67 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_6813 c2_depth c3_depth) (normalization_6816 c2_node c2_sign c3_node)) (and_congr (not_congr (normalization_6813 c2_depth c3_depth)) (normalization_6821 c2_depth c2_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Repair092_68 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair092_61 c2_node c2_sign c3_node c3_sign)) ∨ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_67 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
theorem normalization_6823 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2293 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair092_68 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_6807 c2_depth c3_depth) (normalization_6812 c2_node c2_sign c3_node c3_sign)) (and_congr (not_congr (normalization_6807 c2_depth c3_depth)) (normalization_6822 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

abbrev shared_expr_Repair092_69 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) ∧ False) ∨ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair092_68 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
theorem normalization_6824 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c3_kind = (2 : Int)) ∧ False) ∨ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2293 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))) ↔ (shared_expr_Repair092_69 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_6806 c3_kind) (normalization_1253)) (and_congr (not_congr (normalization_6806 c3_kind)) (normalization_6823 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

abbrev shared_expr_Repair092_70 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (True ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))))) ∨ ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair092_69 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6825 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2294 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ (shared_expr_Repair092_70 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_34 c2_kind) (normalization_6805 c3_kind)) (and_congr (not_congr (normalization_34 c2_kind)) (normalization_6824 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Repair092_71 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ∧ False) ∨ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_70 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6826 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c3_kind = (0 : Int)) ∧ False) ∨ ((¬ (c3_kind = (0 : Int))) ∧ (formula_2294 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))) ↔ (shared_expr_Repair092_71 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_6792 c3_kind) (normalization_1253)) (and_congr (not_congr (normalization_6792 c3_kind)) (normalization_6825 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Repair092_72 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ (shared_expr_Repair092_59 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ∨ ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_71 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6827 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2295 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Repair092_72 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (or_congr (and_congr (normalization_0 c2_kind) (normalization_6803 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) (and_congr (not_congr (normalization_0 c2_kind)) (normalization_6826 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

theorem normalization_6828 (c3_kind : Int) : (¬ (c3_kind = (0 : Int))) ↔ (¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) := (not_congr (normalization_6792 c3_kind))

theorem normalization_6829 (c2_mode c3_mode : Int) : ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ↔ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) := (iff_congr (normalization_1211 c2_mode) (normalization_6793 c3_mode))

theorem normalization_6830 (c2_level c3_level : Int) : (c2_level = c3_level) ↔ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_6831 (c2_mode c3_mode : Int) : (c2_mode = c3_mode) ↔ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) := by
  omega

theorem normalization_6832 (c2_group c3_group : Int) : (c3_group ≤ c2_group) ↔ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6833 (c2_group c3_group : Int) : (¬ (c3_group ≤ c2_group)) ↔ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_6832 c2_group c3_group))

theorem normalization_6834 (c2_mode c3_mode : Int) : (c3_mode ≤ c2_mode) ↔ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6835 (c2_mode c3_mode : Int) : (¬ (c3_mode ≤ c2_mode)) ↔ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_6834 c2_mode c3_mode))

abbrev shared_expr_Repair092_73 (c2_group c2_mode c3_group c3_mode : Int) : Prop := (((((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))) ∨ ((¬ (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))))
theorem normalization_6836 (c2_group c2_mode c3_group c3_mode : Int) : (((c2_mode = c3_mode) ∧ (¬ (c3_group ≤ c2_group))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ (c3_mode ≤ c2_mode)))) ↔ (shared_expr_Repair092_73 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_6831 c2_mode c3_mode) (normalization_6833 c2_group c3_group)) (and_congr (not_congr (normalization_6831 c2_mode c3_mode)) (normalization_6835 c2_mode c3_mode)))

theorem normalization_6837 (c2_level c3_level : Int) : (c3_level ≤ c2_level) ↔ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6838 (c2_level c3_level : Int) : (¬ (c3_level ≤ c2_level)) ↔ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_6837 c2_level c3_level))

abbrev shared_expr_Repair092_74 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair092_73 c2_group c2_mode c3_group c3_mode)) ∨ ((¬ (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))))
theorem normalization_6839 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (((c2_level = c3_level) ∧ (((c2_mode = c3_mode) ∧ (¬ (c3_group ≤ c2_group))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ (c3_mode ≤ c2_mode))))) ∨ ((¬ (c2_level = c3_level)) ∧ (¬ (c3_level ≤ c2_level)))) ↔ (shared_expr_Repair092_74 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6830 c2_level c3_level) (normalization_6836 c2_group c2_mode c3_group c3_mode)) (and_congr (not_congr (normalization_6830 c2_level c3_level)) (normalization_6838 c2_level c3_level)))

abbrev shared_expr_Repair092_75 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair092_74 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
theorem normalization_6840 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2296 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_75 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6829 c2_mode c3_mode) (normalization_6839 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_6829 c2_mode c3_mode)) (normalization_1211 c2_mode)))

theorem normalization_6841 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : ((¬ (c3_kind = (0 : Int))) ∨ (formula_2296 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair092_75 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6828 c3_kind) (normalization_6840 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalization_6842 (c3_kind : Int) : (¬ (c3_kind = (2 : Int))) ↔ (¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) := (not_congr (normalization_6806 c3_kind))

theorem normalization_6843 (c2_node c3_node : Int) : (c3_node ≤ c2_node) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6844 (c2_node c3_node : Int) : (¬ (c3_node ≤ c2_node)) ↔ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6843 c2_node c3_node))

abbrev shared_expr_Repair092_76 (c2_node c2_sign c3_node c3_sign : Int) : Prop := ((shared_expr_Repair092_60 c2_node c2_sign c3_node c3_sign) ∨ ((¬ (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))))))
theorem normalization_6845 (c2_node c2_sign c3_node c3_sign : Int) : (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ (c3_node ≤ c2_node)))) ↔ (shared_expr_Repair092_76 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_6808 c2_node c3_node) (normalization_6810 c2_sign c3_sign)) (and_congr (not_congr (normalization_6808 c2_node c3_node)) (normalization_6844 c2_node c3_node)))

theorem normalization_6846 (c2_depth c3_depth : Int) : (c2_depth = ((-1 : Int) + c3_depth)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_6847 (c2_node c3_node : Int) : ((c3_node / (2 : Int)) ≤ c2_node) ↔ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_6848 (c2_node c3_node : Int) : (¬ ((c3_node / (2 : Int)) ≤ c2_node)) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_6847 c2_node c3_node))

theorem normalization_6849 (c2_node c2_sign c3_node : Int) : (((c2_node = (c3_node / (2 : Int))) ∧ (c2_sign = (0 : Int))) ∨ ((¬ (c2_node = (c3_node / (2 : Int)))) ∧ (¬ ((c3_node / (2 : Int)) ≤ c2_node)))) ↔ (shared_expr_Repair092_63 c2_node c2_sign c3_node) := (or_congr (and_congr (normalization_6814 c2_node c3_node) (normalization_10 c2_sign)) (and_congr (not_congr (normalization_6814 c2_node c3_node)) (normalization_6848 c2_node c3_node)))

theorem normalization_6850 (c2_depth c3_depth : Int) : (c3_depth = ((-1 : Int) + c2_depth)) ↔ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) := by
  omega

theorem normalization_6851 (c2_depth c3_depth : Int) : (¬ (c3_depth = ((-1 : Int) + c2_depth))) ↔ (¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) := (not_congr (normalization_6850 c2_depth c3_depth))

theorem normalization_6852 (c2_node c3_node : Int) : (c3_node ≤ (c2_node / (2 : Int))) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6853 (c2_node c3_node : Int) : (¬ (c3_node ≤ (c2_node / (2 : Int)))) ↔ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6852 c2_node c3_node))

abbrev shared_expr_Repair092_77 (c2_node c3_node : Int) : Prop := ((¬ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int)))) ∧ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))))
abbrev shared_expr_Repair092_78 (c2_node c3_node c3_sign : Int) : Prop := ((((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ∨ (shared_expr_Repair092_77 c2_node c3_node))
theorem normalization_6854 (c2_node c3_node c3_sign : Int) : (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ (¬ (c3_node ≤ (c2_node / (2 : Int)))))) ↔ (shared_expr_Repair092_78 c2_node c3_node c3_sign) := (or_congr (and_congr (normalization_6818 c2_node c3_node) (normalization_6809 c3_sign)) (and_congr (not_congr (normalization_6818 c2_node c3_node)) (normalization_6853 c2_node c3_node)))

theorem normalization_6855 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : ((¬ (c3_depth = ((-1 : Int) + c2_depth))) ∨ (((c3_node = (c2_node / (2 : Int))) ∧ (c3_sign = (1 : Int))) ∨ ((¬ (c3_node = (c2_node / (2 : Int)))) ∧ (¬ (c3_node ≤ (c2_node / (2 : Int))))))) ↔ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair092_78 c2_node c3_node c3_sign)) := (or_congr (normalization_6851 c2_depth c3_depth) (normalization_6854 c2_node c3_node c3_sign))

abbrev shared_expr_Repair092_79 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ ((¬ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)))) ∨ (shared_expr_Repair092_78 c2_node c3_node c3_sign)))
abbrev shared_expr_Repair092_80 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair092_63 c2_node c2_sign c3_node)) ∨ (shared_expr_Repair092_79 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_6856 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2297 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair092_80 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_6846 c2_depth c3_depth) (normalization_6849 c2_node c2_sign c3_node)) (and_congr (not_congr (normalization_6846 c2_depth c3_depth)) (normalization_6855 c2_depth c2_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Repair092_81 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair092_76 c2_node c2_sign c3_node c3_sign)) ∨ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_80 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
theorem normalization_6857 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2298 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair092_81 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_6807 c2_depth c3_depth) (normalization_6845 c2_node c2_sign c3_node c3_sign)) (and_congr (not_congr (normalization_6807 c2_depth c3_depth)) (normalization_6856 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

theorem normalization_6858 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((¬ (c3_kind = (2 : Int))) ∧ (formula_2298 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair092_81 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (and_congr (normalization_6842 c3_kind) (normalization_6857 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

abbrev shared_expr_Repair092_82 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair092_81 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev shared_expr_Repair092_83 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair092_82 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_6859 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2298 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) ↔ (shared_expr_Repair092_83 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_34 c2_kind) (normalization_6804 c3_kind)) (and_congr (not_congr (normalization_34 c2_kind)) (normalization_6858 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

theorem normalization_6860 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2299 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_83 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (and_congr (normalization_6828 c3_kind) (normalization_6859 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Repair092_84 (c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair092_75 c2_group c2_level c2_mode c3_group c3_level c3_mode)))
abbrev shared_expr_Repair092_85 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_83 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6861 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2300 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ ((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_85 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (or_congr (and_congr (normalization_0 c2_kind) (normalization_6841 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) (and_congr (not_congr (normalization_0 c2_kind)) (normalization_6860 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Repair092_86 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((shared_expr_Repair092_72 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ ((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_85 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6862 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2301 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Repair092_86 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_6827 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_6861 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_6098 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2301 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1994 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((c2_mode) ≤ (3 : Int)) ((c3_mode) ≤ (3 : Int)) (((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) (((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (((c2_node + ((-1 : Int) * c3_node)) ≤ (0 : Int)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) ((((c2_sign) ≤ (0 : Int)) ∧ (¬ ((c2_sign) ≤ (-1 : Int)))) ∧ (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int))))) ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Repair092_63 c2_node c2_sign c3_node) ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))) ∧ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int))) ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) (((c3_sign) ≤ (1 : Int)) ∧ (¬ ((c3_sign) ≤ (0 : Int)))) (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6862 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

-- Checked replay of mp.
theorem replay_6099 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i376 : (formula_2295 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2300 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_6098 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) i376

abbrev shared_expr_Repair092_87 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2300 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2300 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2302 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_87 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1995 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

abbrev shared_expr_Repair092_88 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_85 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ ((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_85 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6863 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2302 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Repair092_88 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_6861 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_6861 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_6100 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2302 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1995 ((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_85 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
  have hn := ht
  exact Iff.mpr (normalization_6863 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

-- Checked replay of mp.
theorem replay_6101 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i376 : (formula_2295 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2300 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_6100 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_6099 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i376)

abbrev shared_expr_Repair092_89 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (((c2_level = c3_level) ∧ (((c2_mode = c3_mode) ∧ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))))) ∨ ((¬ (c2_level = c3_level)) ∧ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))))
abbrev formula_2303 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := (shared_expr_Repair092_89 c2_group c2_level c2_mode c3_group c3_level c3_mode)

abbrev shared_expr_Repair092_90 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int))) ∧ (formula_2303 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((c2_mode ≥ (4 : Int)) ↔ (c3_mode ≥ (4 : Int)))) ∧ (c2_mode ≥ (4 : Int))))
abbrev formula_2304 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : Prop := ((¬ (c3_kind = (0 : Int))) ∨ (shared_expr_Repair092_90 c2_group c2_level c2_mode c3_group c3_level c3_mode))

abbrev shared_expr_Repair092_91 (c2_node c2_sign c3_node : Int) : Prop := ((((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ∧ (c2_sign = (0 : Int))) ∨ ((¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)))))
abbrev formula_2305 (c2_node c2_sign c3_node : Int) : Prop := (shared_expr_Repair092_91 c2_node c2_sign c3_node)

abbrev shared_expr_Repair092_92 (c2_node c3_node c3_sign : Int) : Prop := ((((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ∧ (c3_sign = (1 : Int))) ∨ ((¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int))) ∧ (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)))))
abbrev formula_2306 (c2_node c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_92 c2_node c3_node c3_sign)

abbrev shared_expr_Repair092_93 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := ((((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ∧ (formula_2305 c2_node c2_sign c3_node)) ∨ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int))) ∧ ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2306 c2_node c3_node c3_sign))))
abbrev formula_2307 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_93 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_94 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((c2_depth = c3_depth) ∧ (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)))))) ∨ ((¬ (c2_depth = c3_depth)) ∧ (formula_2307 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev formula_2308 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_94 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)

abbrev shared_expr_Repair092_95 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (c3_kind = (0 : Int))) ∧ (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2308 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))))
abbrev formula_2309 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_95 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)

abbrev shared_expr_Repair092_96 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((c2_kind = (0 : Int)) ∧ (formula_2304 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) ∨ ((¬ (c2_kind = (0 : Int))) ∧ (formula_2309 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
abbrev formula_2310 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_96 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

abbrev shared_expr_Repair092_97 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := ((formula_2300 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (formula_2310 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))
abbrev formula_2311 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (shared_expr_Repair092_97 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)

theorem normalized_1996 (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : Prop) : (((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ ((¬ p10) ∧ p11)) ∨ p12))))))))))) ↔ ((p0 ∧ p1) ∨ ((¬ p0) ∧ ((¬ p2) ∧ ((p3 ∧ p4) ∨ ((¬ p3) ∧ ((¬ p5) ∧ ((p6 ∧ p7) ∨ ((¬ p6) ∧ ((p8 ∧ p9) ∨ ((¬ p8) ∧ ((¬ (p11 ∧ (¬ p10))) ∨ p12)))))))))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6864 (c2_group c3_group : Int) : ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)) ↔ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6865 (c2_group c3_group : Int) : (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)))) := (not_congr (normalization_6864 c2_group c3_group))

theorem normalization_6866 (c2_mode c3_mode : Int) : ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)) ↔ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6867 (c2_mode c3_mode : Int) : (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))) := (not_congr (normalization_6866 c2_mode c3_mode))

theorem normalization_6868 (c2_group c2_mode c3_group c3_mode : Int) : (((c2_mode = c3_mode) ∧ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≥ (0 : Int)))) ∨ ((¬ (c2_mode = c3_mode)) ∧ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int))))) ↔ (shared_expr_Repair092_73 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_6831 c2_mode c3_mode) (normalization_6865 c2_group c3_group)) (and_congr (not_congr (normalization_6831 c2_mode c3_mode)) (normalization_6867 c2_mode c3_mode)))

theorem normalization_6869 (c2_level c3_level : Int) : ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)) ↔ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6870 (c2_level c3_level : Int) : (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))) := (not_congr (normalization_6869 c2_level c3_level))

theorem normalization_6871 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2303 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_74 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6830 c2_level c3_level) (normalization_6868 c2_group c2_mode c3_group c3_mode)) (and_congr (not_congr (normalization_6830 c2_level c3_level)) (normalization_6870 c2_level c3_level)))

theorem normalization_6872 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (shared_expr_Repair092_90 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_75 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6829 c2_mode c3_mode) (normalization_6871 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_6829 c2_mode c3_mode)) (normalization_1211 c2_mode)))

theorem normalization_6873 (c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode : Int) : (formula_2304 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair092_75 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (or_congr (normalization_6828 c3_kind) (normalization_6872 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalization_6874 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int)) ↔ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6875 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))) ↔ (¬ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6874 c2_node c3_node))

theorem normalization_6876 (c2_node c2_sign c3_node c3_sign : Int) : (((c2_node = c3_node) ∧ ((c2_sign = (0 : Int)) ∧ (c3_sign = (1 : Int)))) ∨ ((¬ (c2_node = c3_node)) ∧ (¬ ((c2_node + ((-1 : Int) * c3_node)) ≥ (0 : Int))))) ↔ (shared_expr_Repair092_76 c2_node c2_sign c3_node c3_sign) := (or_congr (and_congr (normalization_6808 c2_node c3_node) (normalization_6810 c2_sign c3_sign)) (and_congr (not_congr (normalization_6808 c2_node c3_node)) (normalization_6875 c2_node c3_node)))

theorem normalization_6877 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) = (-1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) := by
  omega

theorem normalization_6878 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (-1 : Int))) ∧ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_6879 (c2_node c3_node : Int) : ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int)) ↔ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int)) := by
  omega

theorem normalization_6880 (c2_node c3_node : Int) : (¬ ((c2_node + ((-1 : Int) * (c3_node / (2 : Int)))) ≥ (0 : Int))) ↔ (¬ (((c3_node / (2 : Int)) + ((-1 : Int) * c2_node)) ≤ (0 : Int))) := (not_congr (normalization_6879 c2_node c3_node))

theorem normalization_6881 (c2_node c2_sign c3_node : Int) : (formula_2305 c2_node c2_sign c3_node) ↔ (shared_expr_Repair092_63 c2_node c2_sign c3_node) := (or_congr (and_congr (normalization_6878 c2_node c3_node) (normalization_10 c2_sign)) (and_congr (not_congr (normalization_6878 c2_node c3_node)) (normalization_6880 c2_node c3_node)))

theorem normalization_6882 (c2_depth c3_depth : Int) : ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int)) ↔ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)))) := by
  omega

theorem normalization_6883 (c2_depth c3_depth : Int) : (¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ↔ (¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) := (not_congr (normalization_6882 c2_depth c3_depth))

theorem normalization_6884 (c2_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) = (0 : Int)) ↔ ((¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) ∧ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (0 : Int))) := by
  omega

theorem normalization_6885 (c2_node c3_node : Int) : ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int)) ↔ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int))) := by
  omega

theorem normalization_6886 (c2_node c3_node : Int) : (¬ ((c3_node + ((-1 : Int) * (c2_node / (2 : Int)))) ≤ (0 : Int))) ↔ (¬ (¬ (((c2_node / (2 : Int)) + ((-1 : Int) * c3_node)) ≤ (-1 : Int)))) := (not_congr (normalization_6885 c2_node c3_node))

theorem normalization_6887 (c2_node c3_node c3_sign : Int) : (formula_2306 c2_node c3_node c3_sign) ↔ (shared_expr_Repair092_78 c2_node c3_node c3_sign) := (or_congr (and_congr (normalization_6884 c2_node c3_node) (normalization_6809 c3_sign)) (and_congr (not_congr (normalization_6884 c2_node c3_node)) (normalization_6886 c2_node c3_node)))

theorem normalization_6888 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : ((¬ ((c2_depth + ((-1 : Int) * c3_depth)) = (1 : Int))) ∨ (formula_2306 c2_node c3_node c3_sign)) ↔ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair092_78 c2_node c3_node c3_sign)) := (or_congr (normalization_6883 c2_depth c3_depth) (normalization_6887 c2_node c3_node c3_sign))

abbrev shared_expr_Repair092_98 (c2_depth c2_node c3_depth c3_node c3_sign : Int) : Prop := ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int))))) ∧ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int))))) ∨ (shared_expr_Repair092_78 c2_node c3_node c3_sign)))
abbrev shared_expr_Repair092_99 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) ∧ (shared_expr_Repair092_63 c2_node c2_sign c3_node)) ∨ (shared_expr_Repair092_98 c2_depth c2_node c3_depth c3_node c3_sign))
theorem normalization_6889 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2307 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair092_99 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_6877 c2_depth c3_depth) (normalization_6881 c2_node c2_sign c3_node)) (and_congr (not_congr (normalization_6877 c2_depth c3_depth)) (normalization_6888 c2_depth c2_node c3_depth c3_node c3_sign)))

abbrev shared_expr_Repair092_100 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : Prop := (((((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) ∧ (shared_expr_Repair092_76 c2_node c2_sign c3_node c3_sign)) ∨ ((¬ (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_99 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
theorem normalization_6890 (c2_depth c2_node c2_sign c3_depth c3_node c3_sign : Int) : (formula_2308 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) ↔ (shared_expr_Repair092_100 c2_depth c2_node c2_sign c3_depth c3_node c3_sign) := (or_congr (and_congr (normalization_6807 c2_depth c3_depth) (normalization_6876 c2_node c2_sign c3_node c3_sign)) (and_congr (not_congr (normalization_6807 c2_depth c3_depth)) (normalization_6889 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))

theorem normalization_6891 (c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : ((¬ (c3_kind = (2 : Int))) ∧ (formula_2308 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) ↔ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair092_100 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)) := (and_congr (normalization_6842 c3_kind) (normalization_6890 c2_depth c2_node c2_sign c3_depth c3_node c3_sign))

abbrev shared_expr_Repair092_101 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int))))) ∧ (shared_expr_Repair092_100 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))
abbrev shared_expr_Repair092_102 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := (((((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) ∧ (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int))))) ∨ (shared_expr_Repair092_101 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))
theorem normalization_6892 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (((c2_kind = (2 : Int)) ∧ (c3_kind = (1 : Int))) ∨ ((¬ (c2_kind = (2 : Int))) ∧ ((¬ (c3_kind = (2 : Int))) ∧ (formula_2308 c2_depth c2_node c2_sign c3_depth c3_node c3_sign)))) ↔ (shared_expr_Repair092_102 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) := (or_congr (and_congr (normalization_34 c2_kind) (normalization_6804 c3_kind)) (and_congr (not_congr (normalization_34 c2_kind)) (normalization_6891 c2_depth c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

theorem normalization_6893 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : (formula_2309 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_102 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (and_congr (normalization_6828 c3_kind) (normalization_6892 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign))

abbrev shared_expr_Repair092_103 (c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign : Int) : Prop := ((¬ (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int))))) ∧ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∧ (shared_expr_Repair092_102 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6894 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2310 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ ((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_103 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) := (or_congr (and_congr (normalization_0 c2_kind) (normalization_6873 c2_group c2_level c2_mode c3_group c3_kind c3_level c3_mode)) (and_congr (not_congr (normalization_0 c2_kind)) (normalization_6893 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))

abbrev shared_expr_Repair092_104 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : Prop := (((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_85 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)) ↔ ((shared_expr_Repair092_84 c2_group c2_kind c2_level c2_mode c3_group c3_kind c3_level c3_mode) ∨ (shared_expr_Repair092_103 c2_depth c2_kind c2_node c2_sign c3_depth c3_kind c3_node c3_sign)))
theorem normalization_6895 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2311 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) ↔ (shared_expr_Repair092_104 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := (iff_congr (normalization_6861 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (normalization_6894 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign))

-- Checked replay of rewrite.
theorem replay_6102 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) : (formula_2311 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  classical
  have ht := (normalized_1996 (((c2_kind) ≤ (0 : Int)) ∧ (¬ ((c2_kind) ≤ (-1 : Int)))) ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ∨ (shared_expr_Repair092_75 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) (((c2_kind) ≤ (2 : Int)) ∧ (¬ ((c2_kind) ≤ (1 : Int)))) (((c3_kind) ≤ (1 : Int)) ∧ (¬ ((c3_kind) ≤ (0 : Int)))) (((c3_kind) ≤ (2 : Int)) ∧ (¬ ((c3_kind) ≤ (1 : Int)))) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)))) (shared_expr_Repair092_76 c2_node c2_sign c3_node c3_sign) (((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-1 : Int)) ∧ (¬ ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (-2 : Int)))) (shared_expr_Repair092_63 c2_node c2_sign c3_node) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (0 : Int)) ((c2_depth + ((-1 : Int) * c3_depth)) ≤ (1 : Int)) (shared_expr_Repair092_78 c2_node c3_node c3_sign))
  have hn := ht
  exact Iff.mpr (normalization_6895 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) hn

-- Checked replay of mp.
theorem replay_6103 (c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign : Int) (i376 : (formula_2295 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign)) : (formula_2310 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) := by
  exact Iff.mp (replay_6102 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign) (replay_6101 c2_depth c2_group c2_kind c2_level c2_mode c2_node c2_sign c3_depth c3_group c3_kind c3_level c3_mode c3_node c3_sign i376)

theorem normalized_1997 (p0 : Prop) : (p0 ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6896 (c3_kind : Int) : (c3_kind ≤ (0 : Int)) ↔ ((c3_kind) ≤ (0 : Int)) := by
  omega

theorem normalization_6897 (c3_kind : Int) : (c3_kind ≥ (0 : Int)) ↔ (¬ ((c3_kind) ≤ (-1 : Int))) := by
  omega

theorem normalization_6898 (c3_kind : Int) : ((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int))) ↔ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) := (and_congr (normalization_6896 c3_kind) (normalization_6897 c3_kind))

theorem normalization_6899 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ ((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int)))) ↔ ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) := (iff_congr (normalization_6792 c3_kind) (normalization_6898 c3_kind))

-- Checked replay of rewrite.
theorem replay_6104 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ ((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int)))) := by
  classical
  have ht := (normalized_1997 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))))
  have hn := ht
  exact Iff.mpr (normalization_6899 c3_kind) hn

theorem normalized_1998 (p0 p1 : Prop) : ((p0 ∧ (¬ p1)) ↔ (¬ ((¬ p0) ∨ (¬ (¬ p1))))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6900 (c3_kind : Int) : (¬ (c3_kind ≤ (0 : Int))) ↔ (¬ ((c3_kind) ≤ (0 : Int))) := (not_congr (normalization_6896 c3_kind))

theorem normalization_6901 (c3_kind : Int) : (¬ (c3_kind ≥ (0 : Int))) ↔ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))) := (not_congr (normalization_6897 c3_kind))

theorem normalization_6902 (c3_kind : Int) : ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))) := (or_congr (normalization_6900 c3_kind) (normalization_6901 c3_kind))

theorem normalization_6903 (c3_kind : Int) : (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := (not_congr (normalization_6902 c3_kind))

theorem normalization_6904 (c3_kind : Int) : (((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := (iff_congr (normalization_6898 c3_kind) (normalization_6903 c3_kind))

-- Checked replay of rewrite.
theorem replay_6105 (c3_kind : Int) : (((c3_kind ≤ (0 : Int)) ∧ (c3_kind ≥ (0 : Int))) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1998 ((c3_kind) ≤ (0 : Int)) ((c3_kind) ≤ (-1 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6904 c3_kind) hn

theorem normalized_1999 (p0 p1 : Prop) : (((p0 ↔ p0) ∧ p1) → p1) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6905 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := (iff_congr (normalization_6792 c3_kind) (normalization_6903 c3_kind))

-- Checked replay of trans.
theorem replay_6106 (c3_kind : Int) : ((c3_kind = (0 : Int)) ↔ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) := by
  classical
  have ht := (normalized_1999 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))))
  have n0 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) := by
    exact Iff.mp (normalization_6899 c3_kind) (replay_6104 c3_kind)
  have n1 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6904 c3_kind) (replay_6105 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6905 c3_kind) hn

theorem normalized_2000 (p0 p1 : Prop) : (((p0 ↔ (¬ p1))) → ((¬ p0) ↔ (¬ (¬ p1)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6906 (c3_kind : Int) : (¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := (not_congr (normalization_6903 c3_kind))

theorem normalization_6907 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))))) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))))) := (iff_congr (normalization_6828 c3_kind) (normalization_6906 c3_kind))

-- Checked replay of monotonicity.
theorem replay_6107 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ (¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))))) := by
  classical
  have ht := (normalized_2000 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))
  have n0 : ((((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ↔ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) := by
    exact Iff.mp (normalization_6905 c3_kind) (replay_6106 c3_kind)
  have hn := ht n0
  exact Iff.mpr (normalization_6907 c3_kind) hn

theorem normalized_2001 (p0 : Prop) : ((¬ (¬ p0)) ↔ p0) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6908 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ↔ ((¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_6906 c3_kind) (normalization_6902 c3_kind))

-- Checked replay of rewrite.
theorem replay_6108 (c3_kind : Int) : ((¬ (¬ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int)))))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_2001 ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))
  have hn := ht
  exact Iff.mpr (normalization_6908 c3_kind) hn

theorem normalized_2002 (p0 p1 : Prop) : ((((¬ p0) ↔ (¬ (¬ p1))) ∧ ((¬ (¬ p1)) ↔ p1)) → ((¬ p0) ↔ p1)) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6909 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) ↔ ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := (iff_congr (normalization_6828 c3_kind) (normalization_6902 c3_kind))

-- Checked replay of trans.
theorem replay_6109 (c3_kind : Int) : ((¬ (c3_kind = (0 : Int))) ↔ ((¬ (c3_kind ≤ (0 : Int))) ∨ (¬ (c3_kind ≥ (0 : Int))))) := by
  classical
  have ht := (normalized_2002 (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int)))) ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))
  have n0 : ((¬ (((c3_kind) ≤ (0 : Int)) ∧ (¬ ((c3_kind) ≤ (-1 : Int))))) ↔ (¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))))) := by
    exact Iff.mp (normalization_6907 c3_kind) (replay_6107 c3_kind)
  have n1 : ((¬ (¬ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int))))))) ↔ ((¬ ((c3_kind) ≤ (0 : Int))) ∨ (¬ (¬ ((c3_kind) ≤ (-1 : Int)))))) := by
    exact Iff.mp (normalization_6908 c3_kind) (replay_6108 c3_kind)
  have hn := ht ⟨n0, n1⟩
  exact Iff.mpr (normalization_6909 c3_kind) hn

abbrev formula_2312 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((shared_expr_Repair092_90 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_39 c2_group c2_level c2_mode c3_group c3_level c3_mode))

theorem normalized_2003 (p0 p1 p2 p3 p4 p5 p6 : Prop) : (((p0 ∧ (((p1 ∧ (¬ p2)) ∧ (((p3 ∧ (¬ p4)) ∧ (¬ (¬ p5))) ∨ ((¬ (p3 ∧ (¬ p4))) ∧ (¬ (¬ p4))))) ∨ ((¬ (p1 ∧ (¬ p2))) ∧ (¬ (¬ p2))))) ∨ ((¬ p0) ∧ (¬ p6))) ↔ ((p0 ∧ ((((¬ p1) ∨ (¬ (¬ p2))) ∧ (¬ (¬ p2))) ∨ ((¬ ((¬ p1) ∨ (¬ (¬ p2)))) ∧ ((((¬ p3) ∨ (¬ (¬ p4))) ∧ (¬ (¬ p4))) ∨ ((¬ ((¬ p3) ∨ (¬ (¬ p4)))) ∧ (¬ (¬ p5))))))) ∨ ((¬ p0) ∧ (¬ p6)))) := by
  classical
  first | (simp only [Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_and_iff_not_or_not, not_or, Classical.not_not, and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or, H4Formal.bool_guard_or, H4Formal.bool_guard_and, H4Formal.bool_guard_or_flip, H4Formal.bool_guard_not_or, H4Formal.bool_guard_not_and, iff_true, iff_false, iff_self]; first | done | (apply Iff.of_eq; ac_rfl)) | (simp only [Classical.not_not, and_assoc, or_assoc, and_comm, or_comm, and_left_comm, or_left_comm, iff_self, iff_true, iff_false, Decidable.or_not_self, Decidable.not_or_self]; done) | (apply Iff.of_eq; ac_rfl) | grind (splits := 1000)

theorem normalization_6910 (c2_level c3_level : Int) : ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ↔ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) := by
  omega

theorem normalization_6911 (c2_level c3_level : Int) : (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ↔ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) := (not_congr (normalization_6910 c2_level c3_level))

theorem normalization_6912 (c2_level c3_level : Int) : ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≥ (0 : Int)))) ↔ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) := (or_congr (normalization_6911 c2_level c3_level) (normalization_6870 c2_level c3_level))

theorem normalization_6913 (c2_mode c3_mode : Int) : ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ↔ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) := by
  omega

theorem normalization_6914 (c2_mode c3_mode : Int) : (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ↔ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) := (not_congr (normalization_6913 c2_mode c3_mode))

theorem normalization_6915 (c2_mode c3_mode : Int) : ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≥ (0 : Int)))) ↔ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) := (or_congr (normalization_6914 c2_mode c3_mode) (normalization_6867 c2_mode c3_mode))

abbrev shared_expr_Repair092_105 (c2_group c2_mode c3_group c3_mode : Int) : Prop := ((((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)))))) ∧ (¬ (¬ ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int))))))
theorem normalization_6916 (c2_group c2_mode c3_group c3_mode : Int) : (formula_2285 c2_group c2_mode c3_group c3_mode) ↔ (shared_expr_Repair092_105 c2_group c2_mode c3_group c3_mode) := (or_congr (and_congr (normalization_6915 c2_mode c3_mode) (normalization_6867 c2_mode c3_mode)) (and_congr (not_congr (normalization_6915 c2_mode c3_mode)) (normalization_6865 c2_group c3_group)))

abbrev shared_expr_Repair092_106 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∧ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int))))) ∨ ((¬ ((¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int))) ∨ (¬ (¬ ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)))))) ∧ (shared_expr_Repair092_105 c2_group c2_mode c3_group c3_mode)))
theorem normalization_6917 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2286 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_106 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6912 c2_level c3_level) (normalization_6870 c2_level c3_level)) (and_congr (not_congr (normalization_6912 c2_level c3_level)) (normalization_6916 c2_group c2_mode c3_group c3_mode)))

abbrev shared_expr_Repair092_107 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : Prop := ((((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ∧ (shared_expr_Repair092_106 c2_group c2_level c2_mode c3_group c3_level c3_mode)) ∨ ((¬ ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int))))) ∧ (¬ ((c2_mode) ≤ (3 : Int)))))
theorem normalization_6918 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (shared_expr_Repair092_39 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_107 c2_group c2_level c2_mode c3_group c3_level c3_mode) := (or_congr (and_congr (normalization_6829 c2_mode c3_mode) (normalization_6917 c2_group c2_level c2_mode c3_group c3_level c3_mode)) (and_congr (not_congr (normalization_6829 c2_mode c3_mode)) (normalization_1211 c2_mode)))

theorem normalization_6919 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2312 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ ((shared_expr_Repair092_75 c2_group c2_level c2_mode c3_group c3_level c3_mode) ↔ (shared_expr_Repair092_107 c2_group c2_level c2_mode c3_group c3_level c3_mode)) := (iff_congr (normalization_6872 c2_group c2_level c2_mode c3_group c3_level c3_mode) (normalization_6918 c2_group c2_level c2_mode c3_group c3_level c3_mode))

-- Checked replay of rewrite.
theorem replay_6110 (c2_group c2_level c2_mode c3_group c3_level c3_mode : Int) : (formula_2312 c2_group c2_level c2_mode c3_group c3_level c3_mode) := by
  classical
  have ht := (normalized_2003 ((¬ ((c2_mode) ≤ (3 : Int))) ↔ (¬ ((c3_mode) ≤ (3 : Int)))) ((c2_level + ((-1 : Int) * c3_level)) ≤ (0 : Int)) ((c2_level + ((-1 : Int) * c3_level)) ≤ (-1 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (0 : Int)) ((c2_mode + ((-1 : Int) * c3_mode)) ≤ (-1 : Int)) ((c2_group + ((-1 : Int) * c3_group)) ≤ (-1 : Int)) ((c2_mode) ≤ (3 : Int)))
  have hn := ht
  exact Iff.mpr (normalization_6919 c2_group c2_level c2_mode c3_group c3_level c3_mode) hn

end H4Formal.Generated.Repair
