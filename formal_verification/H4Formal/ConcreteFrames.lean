import H4Formal.Gadgets
import H4Formal.TerminalForms

namespace H4Formal

def vMode (i : Nat) (s : Sign) : Mode := ⟨.v, i, 0, s⟩
def wMode (i p : Nat) (s : Sign) : Mode := ⟨.w, i, p % 2, s⟩

theorem vPlus_frame (h i p : Nat) (hi : 1 ≤ i)
    (hs : Sign) (hhs : hs = .plus ∨ hs = .leaf) :
    MarkerFrame (asMatrix (originalHost h))
      (.anchor (vMode i .plus) 1) (.anchor (vMode i .plus) 2)
      (.variable i p hs) (.variable (i - 1) (p / 2) .plus)
      (.anchor (vMode i .plus) 1) (.anchor (vMode i .plus) 2)
      .dummy (.variable (i - 1) (p / 2) .plus) := by
  have hn : i ≠ i - 1 := by omega
  have hn' := Ne.symm hn
  have hgt : ¬ i < i - 1 := by omega
  have hdiff : i - (i - 1) = 1 := by omega
  rcases hhs with rfl | rfl <;>
    constructor <;>
    simp [asMatrix, originalHost, IncreasingFour, blockBefore, anchorBefore,
      earlyMode, variableBefore, nodePrefix, vMode, hostValue, role, matchesBlock,
      hn, hn', hgt, hdiff]

theorem vMinus_frame (h i p : Nat) (hi : 1 ≤ i)
    (hs : Sign) (hhs : hs = .minus ∨ hs = .leaf) :
    MarkerFrame (asMatrix (originalHost h))
      (.anchor (vMode i .minus) 1) (.anchor (vMode i .minus) 2)
      (.variable (i - 1) (p / 2) .minus) (.variable i p hs)
      (.anchor (vMode i .minus) 1) (.anchor (vMode i .minus) 2)
      .dummy (.variable (i - 1) (p / 2) .minus) := by
  have hn : i ≠ i - 1 := by omega
  have hn' := Ne.symm hn
  have hlt : i - 1 < i := by omega
  have hdiff : i - (i - 1) = 1 := by omega
  rcases hhs with rfl | rfl <;>
    constructor <;>
    simp [asMatrix, originalHost, IncreasingFour, blockBefore, anchorBefore,
      earlyMode, variableBefore, nodePrefix, vMode, hostValue, role, matchesBlock,
      hn, hn', hlt, hdiff]

theorem wPlus_frame (h i p : Nat) (hi : 1 ≤ i)
    (hs : Sign) (hhs : hs = .plus ∨ hs = .leaf) :
    MarkerFrame (asMatrix (originalHost h))
      (.anchor (wMode i p .plus) 1) (.anchor (wMode i p .plus) 2)
      (.variable i p hs) .dummy
      (.anchor (wMode i p .plus) 1) (.anchor (wMode i p .plus) 2)
      (.variable (i - 1) (p / 2) .plus) (.variable i p hs) := by
  have hn : i ≠ i - 1 := by omega
  have hn' := Ne.symm hn
  have hlt : i - 1 < i := by omega
  have hdiff : i - (i - 1) = 1 := by omega
  rcases hhs with rfl | rfl <;>
    constructor <;>
    simp [asMatrix, originalHost, IncreasingFour, blockBefore, anchorBefore,
      earlyMode, variableBefore, nodePrefix, wMode, hostValue, role, matchesBlock,
      hn, hn', hlt, hdiff]

theorem wMinus_frame (h i p : Nat) (hi : 1 ≤ i)
    (hs : Sign) (hhs : hs = .minus ∨ hs = .leaf) :
    MarkerFrame (asMatrix (originalHost h))
      (.anchor (wMode i p .minus) 1) (.anchor (wMode i p .minus) 2)
      (.variable i p hs) .dummy
      (.anchor (wMode i p .minus) 1) (.anchor (wMode i p .minus) 2)
      (.variable i p hs) (.variable (i - 1) (p / 2) .minus) := by
  have hn : i ≠ i - 1 := by omega
  have hn' := Ne.symm hn
  have hgt : ¬ i < i - 1 := by omega
  have hdiff : i - (i - 1) = 1 := by omega
  rcases hhs with rfl | rfl <;>
    constructor <;>
    simp [asMatrix, originalHost, IncreasingFour, blockBefore, anchorBefore,
      earlyMode, variableBefore, nodePrefix, wMode, hostValue, role, matchesBlock,
      hn, hn', hgt, hdiff]

end H4Formal
