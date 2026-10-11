import H4Formal.Host

namespace H4Formal

/-!
# Lean-side descriptor contract

The SMT corpus uses a seven-field record. This module gives the same record a
Lean representation and proves the canonical encoding/decoding facts for the
finite quotient blocks. It does not import or trust an SMT result.
-/

structure Pos where
  kind : Nat
  mode : Nat
  level : Nat
  group : Nat
  depth : Nat
  node : Nat
  sign : Nat
  deriving DecidableEq, Repr, Inhabited

def modeCode : Mode → Nat
  | { family := .v, sign := .plus, .. } => 0
  | { family := .v, sign := .minus, .. } => 1
  | { family := .w, parity := 0, sign := .plus, .. } => 2
  | { family := .w, parity := 1, sign := .plus, .. } => 3
  | { family := .w, parity := 0, sign := .minus, .. } => 4
  | { family := .w, parity := 1, sign := .minus, .. } => 5
  | _ => 6

def modeFromCode (code level : Nat) : Mode :=
  match code with
  | 0 => { family := .v, depth := level, parity := 0, sign := .plus }
  | 1 => { family := .v, depth := level, parity := 0, sign := .minus }
  | 2 => { family := .w, depth := level, parity := 0, sign := .plus }
  | 3 => { family := .w, depth := level, parity := 1, sign := .plus }
  | 4 => { family := .w, depth := level, parity := 0, sign := .minus }
  | 5 => { family := .w, depth := level, parity := 1, sign := .minus }
  | _ => { family := .v, depth := level, parity := 0, sign := .plus }

def signCode : Sign → Nat
  | .plus => 0
  | .minus => 1
  | .leaf => 2

def signFromCode : Nat → Sign
  | 0 => .plus
  | 1 => .minus
  | _ => .leaf

def allowedMode (m : Mode) : Bool :=
  match m.family, m.sign with
  | .v, .plus => m.parity == 0
  | .v, .minus => m.parity == 0
  | .w, .plus => m.parity < 2
  | .w, .minus => m.parity < 2
  | _, _ => false

theorem mode_code_le_five_of_allowed (m : Mode)
    (hm : allowedMode m = true) : modeCode m ≤ 5 := by
  cases m with
  | mk family depth parity sign =>
    cases family <;> cases sign
    · simp [modeCode]
    · simp [modeCode]
    · simp [allowedMode] at hm
    ·
      have hlt : parity < 2 := by simpa [allowedMode] using hm
      have hp : parity = 0 ∨ parity = 1 := by omega
      rcases hp with hp | hp
      · subst parity
        simp [modeCode]
      · subst parity
        simp [modeCode]
    ·
      have hlt : parity < 2 := by simpa [allowedMode] using hm
      have hp : parity = 0 ∨ parity = 1 := by omega
      rcases hp with hp | hp
      · subst parity
        simp [modeCode]
      · subst parity
        simp [modeCode]
    · simp [allowedMode] at hm

theorem mode_code_of_code (code level : Nat) (hc : code ≤ 5) :
    modeCode (modeFromCode code level) = code := by
  have hcases : code = 0 ∨ code = 1 ∨ code = 2 ∨
      code = 3 ∨ code = 4 ∨ code = 5 := by omega
  rcases hcases with h | h | h | h | h | h <;> subst code <;>
    simp [modeFromCode, modeCode]

theorem mode_from_code_depth (code level : Nat) :
    (modeFromCode code level).depth = level := by
  cases code with
  | zero => rfl
  | succ code =>
    cases code with
    | zero => rfl
    | succ code =>
      cases code with
      | zero => rfl
      | succ code =>
        cases code with
        | zero => rfl
        | succ code =>
          cases code with
          | zero => rfl
          | succ code =>
            cases code with
            | zero => rfl
            | succ code => rfl

theorem allowed_mode_from_code (code level : Nat) (hc : code ≤ 5) :
    allowedMode (modeFromCode code level) = true := by
  have hcases : code = 0 ∨ code = 1 ∨ code = 2 ∨
      code = 3 ∨ code = 4 ∨ code = 5 := by omega
  rcases hcases with h | h | h | h | h | h <;> subst code <;>
    simp [modeFromCode, allowedMode]

theorem sign_code_of_code (code : Nat) (hc : code ≤ 2) :
    signCode (signFromCode code) = code := by
  have hcases : code = 0 ∨ code = 1 ∨ code = 2 := by omega
  rcases hcases with h | h | h <;> subst code <;> rfl

def validBlock (h : Nat) : Block → Bool
  | .anchor m group =>
      1 ≤ m.depth && m.depth ≤ h &&
      (group == 1 || group == 2) && allowedMode m
  | .variable depth node sign =>
      depth ≤ h && node < 2 ^ depth &&
      (if depth = h then sign == .leaf else sign == .plus || sign == .minus)
  | .dummy => true

def validPos (h : Nat) (p : Pos) : Bool :=
  match p.kind with
  | 0 =>
      p.mode ≤ 5 && 1 ≤ p.level && p.level ≤ h &&
      (p.group == 1 || p.group == 2) &&
      p.depth = 0 && p.node = 0 && p.sign = 0
  | 1 =>
      p.mode = 0 && p.level = 0 && p.group = 0 && p.depth ≤ h &&
      p.node < 2 ^ p.depth &&
      (if p.depth = h then p.sign = 2 else p.sign = 0 || p.sign = 1)
  | 2 =>
      p.mode = 0 && p.level = 0 && p.group = 0 &&
      p.depth = 0 && p.node = 0 && p.sign = 0
  | _ => false

def encode : Block → Pos
  | .anchor m group =>
      { kind := 0, mode := modeCode m, level := m.depth, group := group
      , depth := 0, node := 0, sign := 0 }
  | .variable depth node sign =>
      { kind := 1, mode := 0, level := 0, group := 0
      , depth := depth, node := node, sign := signCode sign }
  | .dummy =>
      { kind := 2, mode := 0, level := 0, group := 0
      , depth := 0, node := 0, sign := 0 }

def decode (p : Pos) : Block :=
  match p.kind with
  | 0 => .anchor (modeFromCode p.mode p.level) p.group
  | 1 => .variable p.depth p.node (signFromCode p.sign)
  | _ => .dummy

theorem mode_code_roundtrip (m : Mode)
    (h : allowedMode m = true) : modeFromCode (modeCode m) m.depth = m := by
  cases m with
  | mk family depth parity sign =>
    cases family
    · cases sign
      · have hp : parity = 0 := by simpa [allowedMode] using h
        simp [modeCode, modeFromCode, hp]
      · have hp : parity = 0 := by simpa [allowedMode] using h
        simp [modeCode, modeFromCode, hp]
      · simp [allowedMode] at h
    · cases sign
      · have hp : parity = 0 ∨ parity = 1 := by
          have : parity < 2 := by simpa [allowedMode] using h
          omega
        cases hp with
        | inl hp => simp [modeCode, modeFromCode, hp]
        | inr hp => simp [modeCode, modeFromCode, hp]
      · have hp : parity = 0 ∨ parity = 1 := by
          have : parity < 2 := by simpa [allowedMode] using h
          omega
        cases hp with
        | inl hp => simp [modeCode, modeFromCode, hp]
        | inr hp => simp [modeCode, modeFromCode, hp]
      · simp [allowedMode] at h

theorem sign_code_roundtrip (s : Sign) : signFromCode (signCode s) = s := by
  cases s <;> rfl

theorem valid_encode (h : Nat) (b : Block)
    (hb : validBlock h b = true) : validPos h (encode b) = true := by
  cases b
  · rename_i m g
    simp [validBlock, encode, validPos] at hb ⊢
    cases m with
    | mk family depth parity sign =>
        have hallowed : allowedMode
            { family := family, depth := depth, parity := parity, sign := sign } = true :=
          hb.2
        have hcode : modeCode
            { family := family, depth := depth, parity := parity, sign := sign } ≤ 5 :=
          mode_code_le_five_of_allowed _ hallowed
        cases family <;> cases sign <;>
          simp [modeCode, allowedMode] at * <;> omega
  · rename_i depth node sign
    cases sign
    · have hpl : (Sign.plus == Sign.leaf) = false := by decide
      have hpp : (Sign.plus == Sign.plus) = true := by decide
      have hpm : (Sign.plus == Sign.minus) = false := by decide
      by_cases hd : depth = h
      · simp [validBlock, encode, validPos, signCode, hd, hpl] at hb ⊢
      · simp [validBlock, encode, validPos, signCode, hd, hpp, hpm] at hb ⊢
        exact hb
    · have hml : (Sign.minus == Sign.leaf) = false := by decide
      have hmp : (Sign.minus == Sign.plus) = false := by decide
      have hmm : (Sign.minus == Sign.minus) = true := by decide
      by_cases hd : depth = h
      · simp [validBlock, encode, validPos, signCode, hd, hml] at hb ⊢
      · simp [validBlock, encode, validPos, signCode, hd, hmp, hmm] at hb ⊢
        exact hb
    · have hll : (Sign.leaf == Sign.leaf) = true := by decide
      have hlp : (Sign.leaf == Sign.plus) = false := by decide
      have hlm : (Sign.leaf == Sign.minus) = false := by decide
      by_cases hd : depth = h
      · simp [validBlock, encode, validPos, signCode, hd, hll] at hb ⊢
        exact hb
      · simp [validBlock, encode, validPos, signCode, hd, hlp, hlm] at hb ⊢
  · simp [validBlock, encode, validPos]

theorem decode_encode (h : Nat) (b : Block)
    (hb : validBlock h b = true) : decode (encode b) = b := by
  cases b
  · simp [decode, encode]
    have hb' := hb
    simp [validBlock] at hb'
    exact mode_code_roundtrip _ hb'.2
  · simp [decode, encode, sign_code_roundtrip]
  · rfl

theorem encode_decode (h : Nat) (p : Pos)
    (hp : validPos h p = true) : encode (decode p) = p := by
  cases p with
  | mk kind mode level group depth node sign =>
    cases kind with
    | zero =>
        simp [validPos] at hp
        have hm : mode ≤ 5 := by omega
        have hmode : modeCode (modeFromCode mode level) = mode :=
          mode_code_of_code mode level hm
        have hlevel : (modeFromCode mode level).depth = level :=
          mode_from_code_depth mode level
        simp_all [decode, encode, validPos, modeFromCode, hmode, hlevel]
    | succ kind' =>
        cases kind' with
        | zero =>
            have hs : sign ≤ 2 := by
              by_cases hd : depth = h
              · simp [validPos, hd] at hp
                omega
              · simp [validPos, hd] at hp
                omega
            have hsign : signCode (signFromCode sign) = sign :=
              sign_code_of_code sign hs
            simp_all [decode, encode, validPos, hsign]
        | succ kind'' =>
            cases kind'' with
            | zero =>
                simp [validPos] at hp
                simp_all [decode, encode, validPos]
            | succ _ =>
                simp [validPos] at hp

end H4Formal
