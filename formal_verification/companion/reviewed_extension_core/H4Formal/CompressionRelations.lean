import H4Formal.Host

namespace H4Formal

/-!
# Primitive semantic preservation interface

The concrete depth-compression map is a record transformation.  Its proof
obligations are exposed explicitly here: block constructors, mode equality,
the two role functions, variable-variable values, and terminal-leaf status.
The theorems below are kernel proofs that these primitive obligations imply
preservation of the complete original and repaired host predicates.
-/

def variableValue (h i p : Nat) (rs : Sign) (j q : Nat) (cs : Sign) : Bool :=
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

theorem hostValue_variable_eq (h i p j q : Nat) (rs cs : Sign) :
    hostValue h (.variable i p rs) (.variable j q cs) =
      variableValue h i p rs j q cs := by
  rfl

structure HostCompressionEmbedding (h h' : Nat) where
  map : Block → Block
  mapMode : Mode → Mode
  depthMap : Nat → Nat
  nodeMap : Nat → Nat → Nat
  signMap : Sign → Sign
  map_anchor : ∀ m g,
    map (.anchor m g) = .anchor (mapMode m) g
  map_variable : ∀ d p s,
    map (.variable d p s) = .variable (depthMap d) (nodeMap d p) (signMap s)
  map_dummy : map .dummy = .dummy
  map_ne_dummy : ∀ b, map b = .dummy ↔ b = .dummy
  mode_eq_iff : ∀ m n, mapMode m = mapMode n ↔ m = n
  role_row_variable : ∀ d p s m,
    role (.variable (depthMap d) (nodeMap d p) (signMap s)) (mapMode m) .row =
      role (.variable d p s) m .row
  role_col_variable : ∀ d p s m,
    role (.variable (depthMap d) (nodeMap d p) (signMap s)) (mapMode m) .column =
      role (.variable d p s) m .column
  role_row_dummy : ∀ m,
    role .dummy (mapMode m) .row = role .dummy m .row
  role_col_dummy : ∀ m,
    role .dummy (mapMode m) .column = role .dummy m .column
  variable_value : ∀ i p rs j q cs,
    variableValue h' (depthMap i) (nodeMap i p) (signMap rs)
        (depthMap j) (nodeMap j q) (signMap cs) =
      variableValue h i p rs j q cs
  terminal_preserved : ∀ b,
    isTerminalLeaf h' (map b) = isTerminalLeaf h b

theorem HostCompressionEmbedding.hostValue_preserved
    {h h' : Nat} (e : HostCompressionEmbedding h h')
    (r c : Block) :
    hostValue h' (e.map r) (e.map c) = hostValue h r c := by
  cases r with
  | anchor rm ri =>
      cases c with
      | anchor cm ci =>
          rw [e.map_anchor, e.map_anchor]
          simp [hostValue, e.mode_eq_iff]
      | «variable» cd cp cs =>
          rw [e.map_anchor, e.map_variable]
          simp only [hostValue]
          rw [e.role_col_variable cd cp cs rm]
      | dummy =>
          rw [e.map_anchor, e.map_dummy]
          simp only [hostValue]
          rw [e.role_col_dummy rm]
  | «variable» rd rp rs =>
      cases c with
      | anchor cm ci =>
          rw [e.map_variable, e.map_anchor]
          simp only [hostValue]
          rw [e.role_row_variable rd rp rs cm]
      | «variable» cd cp cs =>
          rw [e.map_variable, e.map_variable]
          change variableValue h' (e.depthMap rd) (e.nodeMap rd rp) (e.signMap rs)
              (e.depthMap cd) (e.nodeMap cd cp) (e.signMap cs) =
            variableValue h rd rp rs cd cp cs
          exact e.variable_value rd rp rs cd cp cs
      | dummy =>
          rw [e.map_variable, e.map_dummy]
          simp [hostValue]
  | dummy =>
      cases c with
      | anchor cm ci =>
          rw [e.map_dummy, e.map_anchor]
          simp only [hostValue]
          rw [e.role_row_dummy cm]
      | «variable» cd cp cs =>
          rw [e.map_dummy, e.map_variable]
          simp [hostValue]
      | dummy =>
          rw [e.map_dummy]
          simp [hostValue]

theorem HostCompressionEmbedding.repairedValue_preserved
    {h h' : Nat} (e : HostCompressionEmbedding h h')
    (r c : Block) :
    repairedValue h' (e.map r) (e.map c) = repairedValue h r c := by
  rw [repairedValue, repairedValue, e.hostValue_preserved]
  by_cases hr : r = .dummy
  · subst r
    rw [e.map_dummy]
    simp [e.terminal_preserved]
  · simp [hr, e.map_ne_dummy]

end H4Formal
