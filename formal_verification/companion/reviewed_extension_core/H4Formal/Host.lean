import H4Formal.Pattern

/-!
# Literal H4 block oracle

The constructor fields and the `role`, `hostValue`, `repairedValue`
definitions follow `src/host.py` and `src/verify_repaired.py`.

Ground translation checks are in `H4Formal/Regression.lean`. The descriptor,
numeric, and bit-vector semantics bridges are in EncodedSemantics,
NatHostBridge, and BVBridge. All-depth results for this Lean specification
are imported by `H4Formal/RemovalObstruction.lean`.
-/

namespace H4Formal

inductive Sign where
  | plus | minus | leaf
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Family where
  | v | w
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Axis where
  | row | column
  deriving DecidableEq, BEq, Repr, Inhabited

structure Mode where
  family : Family
  depth : Nat
  parity : Nat
  sign : Sign
  deriving DecidableEq, Repr, Inhabited

inductive Block where
  | anchor (mode : Mode) (index : Nat)
  | variable (depth node : Nat) (sign : Sign)
  | dummy
  deriving DecidableEq, Repr, Inhabited

/-- The parity restriction is used only for W modes. -/
def matchesBlock (b : Block) (depth : Nat) (sign : Sign)
    (parity : Option Nat := none) : Bool :=
  match b with
  | .variable d p sg =>
      decide (d = depth ∧ (sg = sign ∨ sg = .leaf)) &&
        (match parity with
         | none => true
         | some bit => decide (p % 2 = bit))
  | _ => false

/-- Group number 0, 1, or 2 against a selected marker mode and axis. -/
def role (b : Block) (m : Mode) (axis : Axis) : Nat := Id.run do
  let mut first : Bool := false
  let mut second : Bool := false
  match m.family, axis with
  | .v, .row =>
      if m.sign = .plus then
        first := matchesBlock b m.depth m.sign
        second := matchesBlock b (m.depth - 1) m.sign
      else
        first := matchesBlock b (m.depth - 1) m.sign
        second := matchesBlock b m.depth m.sign
  | .v, .column =>
      first := decide (b = .dummy)
      second := matchesBlock b (m.depth - 1) m.sign
  | .w, .row =>
      first := matchesBlock b m.depth m.sign (some m.parity)
      second := decide (b = .dummy)
  | .w, .column =>
      if m.sign = .plus then
        first := matchesBlock b (m.depth - 1) m.sign
        second := matchesBlock b m.depth m.sign (some m.parity)
      else
        first := matchesBlock b m.depth m.sign (some m.parity)
        second := matchesBlock b (m.depth - 1) m.sign
  return if first then 1 else if second then 2 else 0

/-- Original host entry, before the dummy-row/terminal-leaf repair. -/
def hostValue (h : Nat) (r c : Block) : Bool :=
  match r, c with
  | .anchor mr ri, .anchor mc ci => decide (mr = mc ∧ ri ≠ ci)
  | .anchor m idx, other => decide (role other m .column = idx)
  | other, .anchor m idx => decide (role other m .row = idx)
  | .dummy, _ => true
  | _, .dummy => true
  | .variable i p rs, .variable j q cs =>
      if i = j then
        if rs = .plus ∧ cs = .plus then decide (p ≤ q)
        else if rs = .minus ∧ cs = .minus ∧ i < h then decide (p < q)
        else if rs = .leaf ∧ cs = .leaf ∧ i = h then decide (p ≤ q)
        else false
      else if i = j + 1 then
        if (rs = .plus ∨ rs = .leaf) ∧ cs = .plus then
          decide (p / 2 ≤ q)
        else if (rs = .minus ∨ rs = .leaf) ∧ cs = .minus then
          decide (p / 2 < q)
        else false
      else false

/-- In the original block model, terminal leaves have depth `h`. -/
def isTerminalLeaf (h : Nat) : Block → Bool
  | .variable d _ .leaf => decide (d = h)
  | _ => false

/-- The canonical repair changes exactly dummy-row by terminal-leaf-column. -/
def repairedValue (h : Nat) (r c : Block) : Bool :=
  if r = .dummy ∧ isTerminalLeaf h c = true then false
  else hostValue h r c

theorem repaired_dummy_terminal (h q : Nat) :
    repairedValue h .dummy (.variable h q .leaf) = false := by
  simp [repairedValue, isTerminalLeaf]

theorem repaired_unchanged_outside_dummy (h : Nat) (r c : Block)
    (hr : r ≠ .dummy) :
    repairedValue h r c = hostValue h r c := by
  simp [repairedValue, hr]

theorem original_dummy_terminal (h q : Nat) :
    hostValue h .dummy (.variable h q .leaf) = true := by
  rfl

end H4Formal
