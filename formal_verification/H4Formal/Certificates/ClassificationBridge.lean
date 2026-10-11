import H4Formal.Certificates.CheckedClassification.Classification265
import H4Formal.ArithmeticHost

namespace H4Formal.Arithmetic

set_option maxHeartbeats 500000
set_option maxRecDepth 20000

theorem classification (h : Int) (hh : 1 ≤ h) (r c : Fin 4 → Pos)
    (hc : copy false h r c) :
    terminal h (r 0) (r 1) (r 2) (r 3) (c 0) (c 1) (c 2) (c 3) := by
  classical
  apply Classical.byContradiction
  intro hnt
  exact H4Formal.Generated.Classification.no_counterexample (c (0 : Fin 4)).depth (c (0 : Fin 4)).group (c (0 : Fin 4)).kind (c (0 : Fin 4)).level (c (0 : Fin 4)).mode (c (0 : Fin 4)).node (c (0 : Fin 4)).sign (c (1 : Fin 4)).depth (c (1 : Fin 4)).group (c (1 : Fin 4)).kind (c (1 : Fin 4)).level (c (1 : Fin 4)).mode (c (1 : Fin 4)).node (c (1 : Fin 4)).sign (c (2 : Fin 4)).depth (c (2 : Fin 4)).group (c (2 : Fin 4)).kind (c (2 : Fin 4)).level (c (2 : Fin 4)).mode (c (2 : Fin 4)).node (c (2 : Fin 4)).sign (c (3 : Fin 4)).depth (c (3 : Fin 4)).group (c (3 : Fin 4)).kind (c (3 : Fin 4)).level (c (3 : Fin 4)).mode (c (3 : Fin 4)).node (c (3 : Fin 4)).sign h (r (0 : Fin 4)).depth (r (0 : Fin 4)).group (r (0 : Fin 4)).kind (r (0 : Fin 4)).level (r (0 : Fin 4)).mode (r (0 : Fin 4)).node (r (0 : Fin 4)).sign (r (1 : Fin 4)).depth (r (1 : Fin 4)).group (r (1 : Fin 4)).kind (r (1 : Fin 4)).level (r (1 : Fin 4)).mode (r (1 : Fin 4)).node (r (1 : Fin 4)).sign (r (2 : Fin 4)).depth (r (2 : Fin 4)).group (r (2 : Fin 4)).kind (r (2 : Fin 4)).level (r (2 : Fin 4)).mode (r (2 : Fin 4)).node (r (2 : Fin 4)).sign (r (3 : Fin 4)).depth (r (3 : Fin 4)).group (r (3 : Fin 4)).kind (r (3 : Fin 4)).level (r (3 : Fin 4)).mode (r (3 : Fin 4)).node (r (3 : Fin 4)).sign
    hh
    (by change valid h (r (0 : Fin 4)); exact hc.1 0)
    (by change valid h (r (1 : Fin 4)); exact hc.1 1)
    (by change valid h (r (2 : Fin 4)); exact hc.1 2)
    (by change valid h (r (3 : Fin 4)); exact hc.1 3)
    (by change valid h (c (0 : Fin 4)); exact hc.2.1 0)
    (by change valid h (c (1 : Fin 4)); exact hc.2.1 1)
    (by change valid h (c (2 : Fin 4)); exact hc.2.1 2)
    (by change valid h (c (3 : Fin 4)); exact hc.2.1 3)
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.1 0 1 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.1 0 2 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.1 0 3 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.1 1 2 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.1 1 3 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.1 2 3 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.2.1 0 1 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.2.1 0 2 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.2.1 0 3 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.2.1 1 2 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.2.1 1 3 (by decide))
    (by simpa only [before, modeBefore, varBefore, pIf, eq_self_iff_true,
        Bool.true_eq_false, Bool.false_eq_true] using hc.2.2.2.1 2 3 (by decide))
    (by change (entry false h (r (0 : Fin 4)) (c (1 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 0 1).mpr (by decide))
    (by change (entry false h (r (0 : Fin 4)) (c (2 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 0 2).mpr (by decide))
    (by change (entry false h (r (0 : Fin 4)) (c (3 : Fin 4)) ↔ False)
        simp only [iff_false]
        intro he
        have hp := (hc.2.2.2.2 0 3).mp he
        change false = true at hp
        cases hp)
    (by change (entry false h (r (1 : Fin 4)) (c (0 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 1 0).mpr (by decide))
    (by change (entry false h (r (1 : Fin 4)) (c (1 : Fin 4)) ↔ False)
        simp only [iff_false]
        intro he
        have hp := (hc.2.2.2.2 1 1).mp he
        change false = true at hp
        cases hp)
    (by change (entry false h (r (1 : Fin 4)) (c (2 : Fin 4)) ↔ False)
        simp only [iff_false]
        intro he
        have hp := (hc.2.2.2.2 1 2).mp he
        change false = true at hp
        cases hp)
    (by change (entry false h (r (1 : Fin 4)) (c (3 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 1 3).mpr (by decide))
    (by change (entry false h (r (2 : Fin 4)) (c (0 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 2 0).mpr (by decide))
    (by change (entry false h (r (2 : Fin 4)) (c (1 : Fin 4)) ↔ False)
        simp only [iff_false]
        intro he
        have hp := (hc.2.2.2.2 2 1).mp he
        change false = true at hp
        cases hp)
    (by change (entry false h (r (2 : Fin 4)) (c (2 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 2 2).mpr (by decide))
    (by change (entry false h (r (2 : Fin 4)) (c (3 : Fin 4)) ↔ False)
        simp only [iff_false]
        intro he
        have hp := (hc.2.2.2.2 2 3).mp he
        change false = true at hp
        cases hp)
    (by change (entry false h (r (3 : Fin 4)) (c (0 : Fin 4)) ↔ False)
        simp only [iff_false]
        intro he
        have hp := (hc.2.2.2.2 3 0).mp he
        change false = true at hp
        cases hp)
    (by change (entry false h (r (3 : Fin 4)) (c (1 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 3 1).mpr (by decide))
    (by change (entry false h (r (3 : Fin 4)) (c (2 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 3 2).mpr (by decide))
    (by change (entry false h (r (3 : Fin 4)) (c (3 : Fin 4)) ↔ True)
        simp only [iff_true]
        exact (hc.2.2.2.2 3 3).mpr (by decide))
    (by change ¬ terminal h (r 0) (r 1) (r 2) (r 3) (c 0) (c 1) (c 2) (c 3)
        exact hnt)

end H4Formal.Arithmetic
