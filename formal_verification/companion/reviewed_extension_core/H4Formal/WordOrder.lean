import H4Formal.HostOrderCompression
import Mathlib.Data.List.Lex

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def taggedWord (u : BinaryWord) (tag : Nat) : List Nat :=
  u.map (fun b => if b then 2 else 1) ++ [tag]

def taggedBefore (u v : BinaryWord) (a b : Nat) : Prop :=
  if u <+: v then
    if u.length = v.length then a < b else a = 0
  else if v <+: u then b = 3 else binaryLexLess u v

theorem taggedWord_lt_iff (u v : BinaryWord) (a b : Nat)
    (ha : a = 0 ∨ a = 3) (hb : b = 0 ∨ b = 3) :
    taggedWord u a < taggedWord v b ↔ taggedBefore u v a b := by
  change List.Lex (fun x y : Nat => x < y) (taggedWord u a) (taggedWord v b) ↔
    taggedBefore u v a b
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => simp [taggedWord, taggedBefore, List.lex_singleton_iff]
      | cons c v =>
          rcases ha with rfl | rfl <;> cases c <;>
            simp [taggedWord, taggedBefore, List.cons_lex_cons_iff]
  | cons c u ih =>
      cases v with
      | nil =>
          rcases hb with rfl | rfl <;> cases c <;>
            simp [taggedWord, taggedBefore, List.cons_lex_cons_iff]
      | cons d v =>
          cases c <;> cases d
          · simpa [taggedWord, taggedBefore, List.cons_prefix_cons,
              List.cons_lex_cons_iff, binaryLexLess, bitLT] using ih v
          · simp [taggedWord, taggedBefore, List.cons_prefix_cons,
              List.cons_lex_cons_iff, binaryLexLess, bitLT]
          · simp [taggedWord, taggedBefore, List.cons_prefix_cons,
              List.cons_lex_cons_iff, binaryLexLess, bitLT]
          · simpa [taggedWord, taggedBefore, List.cons_prefix_cons,
              List.cons_lex_cons_iff, binaryLexLess, bitLT] using ih v

theorem taggedWord_eq_iff (u v : BinaryWord) (a b : Nat)
    (ha : a = 0 ∨ a = 3) (hb : b = 0 ∨ b = 3) :
    taggedWord u a = taggedWord v b ↔ u = v ∧ a = b := by
  constructor
  · intro he
    induction u generalizing v with
    | nil =>
        cases v with
        | nil => simpa [taggedWord] using he
        | cons c v =>
            rcases ha with rfl | rfl <;> cases c <;> simp [taggedWord] at he
    | cons c u ih =>
        cases v with
        | nil =>
            rcases hb with rfl | rfl <;> cases c <;> simp [taggedWord] at he
        | cons d v =>
            cases c <;> cases d <;> simp only [taggedWord, List.map_cons, List.cons_append] at he
            · obtain ⟨hu, ht⟩ := ih v (List.cons.inj he).2
              exact ⟨congrArg (List.cons false) hu, ht⟩
            · simp at he
            · simp at he
            · obtain ⟨hu, ht⟩ := ih v (List.cons.inj he).2
              exact ⟨congrArg (List.cons true) hu, ht⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def endTag (axis : Axis) : Sign → Nat
  | .plus => if axis = .row then 3 else 0
  | .minus => if axis = .row then 0 else 3
  | .leaf => 0

theorem endTag_range (axis : Axis) (sign : Sign) :
    endTag axis sign = 0 ∨ endTag axis sign = 3 := by
  cases axis <;> cases sign <;> simp [endTag]

def ValidSignAt (h d : Nat) (sign : Sign) : Prop :=
  d ≤ h ∧ if d = h then sign = .leaf else sign = .plus ∨ sign = .minus

theorem ValidSignAt.not_leaf {h d : Nat} {sign : Sign}
    (hv : ValidSignAt h d sign) (hd : d < h) : sign ≠ .leaf := by
  have hcases : sign = .plus ∨ sign = .minus := by
    simpa only [ValidSignAt, if_neg (Nat.ne_of_lt hd)] using hv.2
  rcases hcases with rfl | rfl <;> decide

theorem endTag_zero_iff (axis : Axis) (sign : Sign) (hn : sign ≠ .leaf) :
    endTag axis sign = 0 ↔ ancestorSignBefore axis sign := by
  cases axis <;> cases sign <;> simp [endTag, ancestorSignBefore] at hn ⊢

theorem endTag_three_iff (axis : Axis) (sign : Sign) :
    endTag axis sign = 3 ↔ descendantSignBefore axis sign := by
  cases axis <;> cases sign <;> simp [endTag, descendantSignBefore]

theorem endTag_lt_same_depth (h d : Nat) (axis : Axis) (r c : Sign)
    (hr : ValidSignAt h d r) (hc : ValidSignAt h d c) :
    endTag axis r < endTag axis c ↔ sameDepthSignBefore axis r c := by
  by_cases hd : d = h
  · have er : r = .leaf := by simpa only [if_pos hd] using hr.2
    have ec : c = .leaf := by simpa only [if_pos hd] using hc.2
    subst r
    subst c
    cases axis <;> simp [endTag, sameDepthSignBefore]
  · have er : r = .plus ∨ r = .minus := by simpa only [if_neg hd] using hr.2
    have ec : c = .plus ∨ c = .minus := by simpa only [if_neg hd] using hc.2
    rcases er with rfl | rfl <;> rcases ec with rfl | rfl <;>
      cases axis <;> simp [endTag, sameDepthSignBefore]

theorem variableBefore_tagged (h : Nat) (axis : Axis) (u v : BinaryWord) (r c : Sign)
    (hr : ValidSignAt h u.length r) (hc : ValidSignAt h v.length c) :
    taggedWord u (endTag axis r) < taggedWord v (endTag axis c) ↔
      variableBefore axis ⟨u, r⟩ ⟨v, c⟩ := by
  rw [taggedWord_lt_iff u v _ _ (endTag_range axis r) (endTag_range axis c)]
  by_cases hp : u <+: v
  · by_cases hl : u.length = v.length
    · have hc' : ValidSignAt h u.length c := by simpa only [hl] using hc
      simp only [taggedBefore, variableBefore, hp, hl, if_true]
      exact endTag_lt_same_depth h u.length axis r c hr hc'
    · have hlt : u.length < h := by
        have hle := hp.length_le
        have hbound := hc.1
        omega
      simp only [taggedBefore, variableBefore, hp, hl, if_true, if_false]
      exact endTag_zero_iff axis r (hr.not_leaf hlt)
  · by_cases hq : v <+: u
    · simp only [taggedBefore, variableBefore, hp, hq, if_true, if_false]
      exact endTag_three_iff axis c
    · simp [taggedBefore, variableBefore, hp, hq]

end H4Formal
