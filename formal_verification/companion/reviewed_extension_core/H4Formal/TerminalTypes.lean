import H4Formal.Host

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

def terminalMode (h parity : Nat) : Mode :=
  { family := .w, depth := h, parity := parity, sign := .minus }

def TerminalForm (h : Nat) (rows cols : Fin 4 → Block) : Prop :=
  ∃ parity p, parity < 2 ∧ p < 2 ^ h ∧ p % 2 = parity ∧
    rows 0 = .anchor (terminalMode h parity) 1 ∧
    rows 1 = .anchor (terminalMode h parity) 2 ∧
    rows 2 = .variable h p .leaf ∧ rows 3 = .dummy ∧
    cols 0 = .anchor (terminalMode h parity) 1 ∧
    cols 2 = .variable h p .leaf ∧
    cols 3 = .variable (h - 1) (p / 2) .minus ∧
    (cols 1 = .anchor (terminalMode h parity) 2 ∨
      ∃ q, q < p ∧ q % 2 = p % 2 ∧ cols 1 = .variable h q .leaf)

end H4Formal
