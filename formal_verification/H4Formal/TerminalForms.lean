import H4Formal.ValidHost
import H4Formal.Matrix

namespace H4Formal

def terminalMode (h p : Nat) : Mode := ⟨.w, h, p % 2, .minus⟩

def terminalRows (h p : Nat) : Fin 4 → Block :=
  four (.anchor (terminalMode h p) 1) (.anchor (terminalMode h p) 2)
    (.variable h p .leaf) .dummy

def terminalIColumns (h p : Nat) : Fin 4 → Block :=
  four (.anchor (terminalMode h p) 1) (.anchor (terminalMode h p) 2)
    (.variable h p .leaf) (.variable (h - 1) (p / 2) .minus)

def terminalIIColumns (h p q : Nat) : Fin 4 → Block :=
  four (.anchor (terminalMode h p) 1) (.variable h q .leaf)
    (.variable h p .leaf) (.variable (h - 1) (p / 2) .minus)

def asMatrix (H : OrderedBlockHost) : OrderedMatrix Block Block where
  value := H.value
  rowBefore := H.rowBefore
  colBefore := H.colBefore

theorem copy_asMatrix (H : OrderedBlockHost) (r c : Fin 4 → Block) :
    MatrixCopy (asMatrix H) r c ↔ IsCopy H r c := Iff.rfl

theorem terminalI_isCopy (h p : Nat) (hh : 1 ≤ h) :
    IsCopy (originalHost h) (terminalRows h p) (terminalIColumns h p) := by
  have hn : h ≠ h - 1 := by omega
  have hn' : h - 1 ≠ h := Ne.symm hn
  have hgt : ¬ h < h - 1 := by omega
  have hprev : h - 1 + 1 = h := by omega
  have hdiff : h - (h - 1) = 1 := by omega
  apply (copy_asMatrix _ _ _).1
  apply (matrixCopy_four_iff _ _ _ _ _ _ _ _ _).2
  simp [asMatrix, originalHost, IncreasingFour,
    blockBefore, anchorBefore, earlyMode, variableBefore, nodePrefix,
    terminalMode, hostValue, role, matchesBlock, hn, hn', hgt, hprev, hdiff]

theorem terminalII_isCopy (h p q : Nat) (hh : 1 ≤ h) (hqp : q < p)
    (hparity : q % 2 = p % 2) :
    IsCopy (originalHost h) (terminalRows h p) (terminalIIColumns h p q) := by
  have hn : h ≠ h - 1 := by omega
  have hn' : h - 1 ≠ h := Ne.symm hn
  have hgt : ¬ h < h - 1 := by omega
  have hprev : h - 1 + 1 = h := by omega
  have hdiff : h - (h - 1) = 1 := by omega
  have hparents : q / 2 < p / 2 := by omega
  have hpq : ¬ p ≤ q := by omega
  have hqqp : q ≠ p := by omega
  apply (copy_asMatrix _ _ _).1
  apply (matrixCopy_four_iff _ _ _ _ _ _ _ _ _).2
  simp [asMatrix, originalHost, IncreasingFour,
    blockBefore, anchorBefore, earlyMode, variableBefore, nodePrefix,
    terminalMode, hostValue, role, matchesBlock, hn, hn', hgt, hprev, hdiff,
    hparents, hpq, hqqp, hqp, hparity]

theorem terminalMode_valid (h p : Nat) (hh : 1 ≤ h) :
    ValidMode h (terminalMode h p) := by
  simp [ValidMode, terminalMode]
  exact ⟨hh, Nat.mod_lt p (by decide)⟩

theorem terminal_parent_valid (h p : Nat) (hh : 1 ≤ h) (hp : p < 2 ^ h) :
    ValidBlock h (.variable (h - 1) (p / 2) .minus) := by
  have hn : h - 1 ≠ h := by omega
  have hpow : 2 ^ h = 2 ^ (h - 1) * 2 := by
    exact (Nat.two_pow_pred_mul_two hh).symm
  have hparent : p / 2 < 2 ^ (h - 1) := by
    rw [hpow] at hp
    omega
  simp [ValidBlock, hn]
  exact hparent

theorem terminalI_validCopy (h p : Nat) (hh : 1 ≤ h) (hp : p < 2 ^ h) :
    ValidCopy h (originalHost h) (terminalRows h p) (terminalIColumns h p) := by
  have hm := terminalMode_valid h p hh
  have hparent := terminal_parent_valid h p hh hp
  refine ⟨?_, ?_, terminalI_isCopy h p hh⟩
  · simp [terminalRows, Fin.forall_fin_succ, four, ValidBlock, hm, hp]
  · simp [terminalIColumns, Fin.forall_fin_succ, four, ValidBlock, hm, hp] at hparent ⊢
    exact hparent

theorem terminalII_validCopy (h p q : Nat) (hh : 1 ≤ h) (hp : p < 2 ^ h)
    (hqp : q < p) (hparity : q % 2 = p % 2) :
    ValidCopy h (originalHost h) (terminalRows h p) (terminalIIColumns h p q) := by
  have hm := terminalMode_valid h p hh
  have hparent := terminal_parent_valid h p hh hp
  have hq : q < 2 ^ h := by omega
  refine ⟨?_, ?_, terminalII_isCopy h p q hh hqp hparity⟩
  · simp [terminalRows, Fin.forall_fin_succ, four, ValidBlock, hm, hp]
  · simp [terminalIIColumns, Fin.forall_fin_succ, four, ValidBlock, hm, hp, hq] at hparent ⊢
    exact hparent

theorem terminalI_destroyed_by_repair (h p : Nat) :
    ¬ IsCopy (canonicalHost h) (terminalRows h p) (terminalIColumns h p) := by
  intro hc
  have cell := hc.2.2 (3 : Fin 4) (2 : Fin 4)
  simp [canonicalHost, terminalRows, terminalIColumns, four, pattern,
    repairedValue, isTerminalLeaf] at cell

theorem terminalII_destroyed_by_repair (h p q : Nat) :
    ¬ IsCopy (canonicalHost h) (terminalRows h p) (terminalIIColumns h p q) := by
  intro hc
  have cell := hc.2.2 (3 : Fin 4) (2 : Fin 4)
  simp [canonicalHost, terminalRows, terminalIIColumns, four, pattern,
    repairedValue, isTerminalLeaf] at cell

end H4Formal
