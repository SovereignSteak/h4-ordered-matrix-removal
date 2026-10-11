import H4Formal.QuerySemantics

namespace H4Formal

/-!
# Field-level entry semantics

The SMT input stores a block as seven bounded fields.  The definitions below
restate the entry calculation over those fields and prove that encoding a
valid Lean block gives the same Boolean value as `hostValue`.  This closes the
local representation bridge used by the finite queries; it does not certify a
solver's UNSAT result.
-/

def encodedModeBefore (minusFirst : Bool) (x y : Pos) : Bool :=
  if minusFirst then
    let xFirst := 4 ≤ x.mode
    let yFirst := 4 ≤ y.mode
    if xFirst != yFirst then xFirst
    else if x.level != y.level then x.level < y.level
    else if x.mode != y.mode then x.mode < y.mode
    else x.group < y.group
  else if x.level != y.level then x.level < y.level
  else if x.mode != y.mode then x.mode < y.mode
  else x.group < y.group

def encodedVarBefore (isRow : Bool) (x y : Pos) : Bool :=
  if x.depth = y.depth then
    if x.node = y.node then
      if isRow then x.sign = 1 && y.sign = 0
      else x.sign = 0 && y.sign = 1
    else x.node < y.node
  else if x.depth < y.depth then
    let yPrefix := y.node / 2 ^ (y.depth - x.depth)
    if x.node = yPrefix then
      if isRow then x.sign = 1 else x.sign = 0
    else x.node < yPrefix
  else
    let xPrefix := x.node / 2 ^ (x.depth - y.depth)
    if y.node = xPrefix then
      if isRow then y.sign = 0 else y.sign = 1
    else xPrefix < y.node

def encodedComesBefore (minusFirst isRow : Bool) (x y : Pos) : Bool :=
  if x.kind = 0 then
    if y.kind = 0 then encodedModeBefore minusFirst x y else true
  else if y.kind = 0 then false
  else if x.kind = 2 then !isRow && y.kind = 1
  else if y.kind = 2 then isRow
  else encodedVarBefore isRow x y

def hostModeBefore (minusFirst : Bool)
    (xm ym : Mode) (xg yg : Nat) : Bool :=
  let xFirst := 4 ≤ modeCode xm
  let yFirst := 4 ≤ modeCode ym
  if minusFirst then
    if xFirst != yFirst then xFirst
    else if xm.depth != ym.depth then xm.depth < ym.depth
    else if modeCode xm != modeCode ym then modeCode xm < modeCode ym
    else xg < yg
  else if xm.depth != ym.depth then xm.depth < ym.depth
  else if modeCode xm != modeCode ym then modeCode xm < modeCode ym
  else xg < yg

def hostVariableBefore (isRow : Bool)
    (rd rp : Nat) (rs : Sign) (cd cp : Nat) (cs : Sign) : Bool :=
  if rd = cd then
    if rp = cp then
      if isRow then signCode rs = 1 && signCode cs = 0
      else signCode rs = 0 && signCode cs = 1
    else rp < cp
  else if rd < cd then
    let cPrefix := cp / 2 ^ (cd - rd)
    if rp = cPrefix then
      if isRow then signCode rs = 1 else signCode rs = 0
    else rp < cPrefix
  else
    let rPrefix := rp / 2 ^ (rd - cd)
    if cp = rPrefix then
      if isRow then signCode cs = 0 else signCode cs = 1
    else rPrefix < cp

def hostComesBefore (minusFirst isRow : Bool) (r c : Block) : Bool :=
  match r, c with
  | .anchor rm rg, .anchor cm cg => hostModeBefore minusFirst rm cm rg cg
  | .anchor _ _, _ => true
  | _, .anchor _ _ => false
  | .dummy, .variable _ _ _ => !isRow
  | .dummy, .dummy => false
  | .variable _ _ _, .dummy => isRow
  | .variable rd rp rs, .variable cd cp cs =>
      hostVariableBefore isRow rd rp rs cd cp cs

theorem encodedModeBefore_encode_anchor
    (minusFirst : Bool) (xm ym : Mode) (xg yg : Nat) :
    encodedModeBefore minusFirst
        (encode (.anchor xm xg)) (encode (.anchor ym yg)) =
      hostModeBefore minusFirst xm ym xg yg := by
  simp [encodedModeBefore, hostModeBefore, encode]

theorem encodedVarBefore_encode_variable
    (isRow : Bool) (rd rp : Nat) (rs : Sign)
    (cd cp : Nat) (cs : Sign) :
    encodedVarBefore isRow
        (encode (.variable rd rp rs)) (encode (.variable cd cp cs)) =
      hostVariableBefore isRow rd rp rs cd cp cs := by
  simp [encodedVarBefore, hostVariableBefore, encode, signCode]

theorem encodedComesBefore_encode
    (minusFirst isRow : Bool) (r c : Block) :
    encodedComesBefore minusFirst isRow (encode r) (encode c) =
      hostComesBefore minusFirst isRow r c := by
  cases r <;> cases c <;>
    simp [encodedComesBefore, hostComesBefore, encodedModeBefore,
      hostModeBefore, encodedVarBefore, hostVariableBefore, encode, signCode]

def encodedRole (anchor value : Pos) (axis : Axis) : Nat :=
  role (decode value) (modeFromCode anchor.mode anchor.level) axis

def encodedVariableValue (h : Nat) (r c : Pos) : Bool :=
  if r.depth = c.depth then
    if r.sign = 0 ∧ c.sign = 0 then decide (r.node ≤ c.node)
    else if r.sign = 1 ∧ c.sign = 1 ∧ r.depth < h then
      decide (r.node < c.node)
    else if r.sign = 2 ∧ c.sign = 2 ∧ r.depth = h then
      decide (r.node ≤ c.node)
    else false
  else if r.depth = c.depth + 1 then
    if (r.sign = 0 ∨ r.sign = 2) ∧ c.sign = 0 then
      decide (r.node / 2 ≤ c.node)
    else if (r.sign = 1 ∨ r.sign = 2) ∧ c.sign = 1 then
      decide (r.node / 2 < c.node)
    else false
  else false

def encodedEntry (h : Nat) (r c : Pos) : Bool :=
  match r.kind, c.kind with
  | 0, 0 => decide
      (modeFromCode r.mode r.level = modeFromCode c.mode c.level ∧
        r.group ≠ c.group)
  | 0, _ => decide (encodedRole r c .column = r.group)
  | _, 0 => decide (encodedRole c r .row = c.group)
  | 2, _ => true
  | _, 2 => true
  | 1, 1 => encodedVariableValue h r c
  | _, _ => false

theorem encodedEntry_encode
    (h : Nat) (r c : Block)
    (hr : validBlock h r = true) (hc : validBlock h c = true) :
    encodedEntry h (encode r) (encode c) = hostValue h r c := by
  cases r with
  | anchor rm ri =>
      have hmr : allowedMode rm = true := by
        have h := hr
        simp [validBlock] at h
        exact h.2
      cases c with
      | anchor cm ci =>
          have hmc : allowedMode cm = true := by
            have h := hc
            simp [validBlock] at h
            exact h.2
          have hmr' : modeFromCode (modeCode rm) rm.depth = rm :=
            mode_code_roundtrip rm hmr
          have hmc' : modeFromCode (modeCode cm) cm.depth = cm :=
            mode_code_roundtrip cm hmc
          simp [encodedEntry, encode, hmr', hmc', hostValue]
      | «variable» cd cp cs =>
          have hc' : decode (encode (.variable cd cp cs)) =
              .variable cd cp cs := decode_encode h _ hc
          have hs' : signFromCode (signCode cs) = cs :=
            sign_code_roundtrip cs
          have hm' : modeFromCode (modeCode rm) rm.depth = rm :=
            mode_code_roundtrip rm hmr
          simp [encodedEntry, encodedRole, encode, decode, hm', hc', hs',
            hostValue]
      | dummy =>
          have hm' : modeFromCode (modeCode rm) rm.depth = rm :=
            mode_code_roundtrip rm hmr
          simp [encodedEntry, encodedRole, encode, decode, hm', hostValue]
  | «variable» rd rp rs =>
      cases c with
      | anchor cm ci =>
          have hmc : allowedMode cm = true := by
            have h := hc
            simp [validBlock] at h
            exact h.2
          have hm' : modeFromCode (modeCode cm) cm.depth = cm :=
            mode_code_roundtrip cm hmc
          have hr' : decode (encode (.variable rd rp rs)) =
              .variable rd rp rs := decode_encode h _ hr
          have hs' : signFromCode (signCode rs) = rs :=
            sign_code_roundtrip rs
          simp [encodedEntry, encodedRole, encode, decode, hm', hr', hs',
            hostValue]
      | «variable» cd cp cs =>
          cases rs <;> cases cs <;>
            simp [encodedEntry, encodedVariableValue, encode, hostValue,
              signCode]
      | dummy =>
          simp [encodedEntry, encodedVariableValue, encode, hostValue]
  | dummy =>
      cases c with
      | anchor cm ci =>
          have hmc : allowedMode cm = true := by
            have h := hc
            simp [validBlock] at h
            exact h.2
          have hm' : modeFromCode (modeCode cm) cm.depth = cm :=
            mode_code_roundtrip cm hmc
          simp [encodedEntry, encodedRole, encode, decode, hm', hostValue]
      | «variable» cd cp cs =>
          simp [encodedEntry, encodedRole, encode, decode, hostValue]
      | dummy =>
          simp [encodedEntry, encodedRole, encode, decode, hostValue]

end H4Formal
