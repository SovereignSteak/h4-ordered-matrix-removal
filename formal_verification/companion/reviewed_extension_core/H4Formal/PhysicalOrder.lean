import H4Formal.PhysicalHostCore
import H4Formal.WordOrder
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Sort

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def blockOrderKey (axis : Axis) : Block → List Nat
  | .anchor mode group =>
      [0, if 4 ≤ modeCode mode then 0 else 1, mode.depth, modeCode mode, group]
  | .variable d p sign =>
      (if axis = .row then 1 else 2) :: taggedWord (natWord d p) (endTag axis sign)
  | .dummy => [if axis = .row then 2 else 1]

theorem valid_variable_sign {h d p : Nat} {sign : Sign}
    (hv : validBlock h (.variable d p sign) = true) : ValidSignAt h d sign := by
  have hpl : (Sign.plus == Sign.leaf) = false := by decide
  have hml : (Sign.minus == Sign.leaf) = false := by decide
  have hlp : (Sign.leaf == Sign.plus) = false := by decide
  have hlm : (Sign.leaf == Sign.minus) = false := by decide
  by_cases hd : d = h
  · cases sign <;> simp_all [validBlock, ValidSignAt]
  · cases sign <;> simp_all [validBlock, ValidSignAt]

theorem valid_variable_node {h d p : Nat} {sign : Sign}
    (hv : validBlock h (.variable d p sign) = true) : p < 2 ^ d := by
  simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.1.2

theorem endTag_injective_at (h d : Nat) (axis : Axis) (r c : Sign)
    (hr : ValidSignAt h d r) (hc : ValidSignAt h d c)
    (he : endTag axis r = endTag axis c) : r = c := by
  by_cases hd : d = h
  · have er : r = .leaf := by simpa only [if_pos hd] using hr.2
    have ec : c = .leaf := by simpa only [if_pos hd] using hc.2
    exact er.trans ec.symm
  · have er : r = .plus ∨ r = .minus := by simpa only [if_neg hd] using hr.2
    have ec : c = .plus ∨ c = .minus := by simpa only [if_neg hd] using hc.2
    rcases er with rfl | rfl <;> rcases ec with rfl | rfl <;>
      cases axis <;> simp_all [endTag]

theorem blockOrderKey_eq_iff (h : Nat) (axis : Axis) (r c : Block)
    (hr : validBlock h r = true) (hc : validBlock h c = true) :
    blockOrderKey axis r = blockOrderKey axis c ↔ r = c := by
  constructor
  · intro he
    cases r with
    | anchor rm rg =>
        cases c with
        | anchor cm cg =>
            have hv := hr
            have hw := hc
            simp only [validBlock, Bool.and_eq_true] at hv hw
            simp [blockOrderKey] at he
            obtain ⟨_, hd, hm, hg⟩ := he
            have hmode : rm = cm := by
              rw [← mode_code_roundtrip rm hv.2, ← mode_code_roundtrip cm hw.2]
              rw [hd, hm]
            simp only [hmode, hg]
        | «variable» d p sign =>
            cases axis <;> simp [blockOrderKey] at he
        | dummy => cases axis <;> simp [blockOrderKey] at he
    | «variable» rd rp rs =>
        cases c with
        | anchor cm cg => cases axis <;> simp [blockOrderKey] at he
        | «variable» cd cp cs =>
            have htag : taggedWord (natWord rd rp) (endTag axis rs) =
                taggedWord (natWord cd cp) (endTag axis cs) := (List.cons.inj he).2
            obtain ⟨hw, ht⟩ := (taggedWord_eq_iff _ _ _ _
              (endTag_range axis rs) (endTag_range axis cs)).mp htag
            have hd : rd = cd := by simpa using congrArg List.length hw
            have hn : rp = cp := by
              simpa only [wordNat_natWord rd rp (valid_variable_node hr),
                wordNat_natWord cd cp (valid_variable_node hc)] using congrArg wordNat hw
            have hs : rs = cs := endTag_injective_at h rd axis rs cs
              (valid_variable_sign hr) (by simpa only [hd] using valid_variable_sign hc) ht
            simp only [hd, hn, hs]
        | dummy =>
            cases axis <;> simp [blockOrderKey] at he
    | dummy =>
        cases c with
        | anchor cm cg => cases axis <;> simp [blockOrderKey] at he
        | «variable» d p sign => cases axis <;> simp [blockOrderKey] at he
        | dummy => rfl
  · rintro rfl
    rfl

theorem blockOrderKey_lt_iff (h : Nat) (axis : Axis) (r c : Block)
    (hr : validBlock h r = true) (hc : validBlock h c = true) :
    blockOrderKey axis r < blockOrderKey axis c ↔
      hostComesBefore true (axis == .row) r c = true := by
  change List.Lex (fun x y : Nat => x < y) (blockOrderKey axis r)
    (blockOrderKey axis c) ↔ _
  cases r with
  | anchor rm rg =>
      cases c with
      | anchor cm cg =>
          by_cases hf : 4 ≤ modeCode rm <;> by_cases hg : 4 ≤ modeCode cm <;>
            by_cases hd : rm.depth = cm.depth <;>
            by_cases hm : modeCode rm = modeCode cm <;>
            simp [blockOrderKey, hostComesBefore, hostModeBefore,
              List.cons_lex_cons_iff, hf, hg, hd, hm]
      | «variable» d p sign =>
          cases axis <;> simp [blockOrderKey, hostComesBefore, List.cons_lex_cons_iff]
      | dummy =>
          cases axis <;> simp [blockOrderKey, hostComesBefore, List.cons_lex_cons_iff]
  | «variable» rd rp rs =>
      cases c with
      | anchor cm cg =>
          cases axis <;> simp [blockOrderKey, hostComesBefore, List.cons_lex_cons_iff]
      | «variable» cd cp cs =>
          simp only [blockOrderKey, List.lex_cons_iff, hostComesBefore]
          have hleft := variableBefore_tagged h axis (natWord rd rp) (natWord cd cp) rs cs
            (by simpa using valid_variable_sign hr) (by simpa using valid_variable_sign hc)
          have hright := hostVariableBefore_words axis (natWord rd rp) (natWord cd cp) rs cs
          simp only [natWord_length, wordNat_natWord rd rp (valid_variable_node hr),
            wordNat_natWord cd cp (valid_variable_node hc)] at hright
          exact hleft.trans hright.symm
      | dummy =>
          cases axis <;> simp [blockOrderKey, hostComesBefore, List.cons_lex_cons_iff] <;> decide
  | dummy =>
      cases c with
      | anchor cm cg =>
          cases axis <;> simp [blockOrderKey, hostComesBefore, List.cons_lex_cons_iff]
      | «variable» d p sign =>
          cases axis <;> simp [blockOrderKey, hostComesBefore, List.cons_lex_cons_iff] <;> decide
      | dummy =>
          cases axis <;> simp [blockOrderKey, hostComesBefore, List.lex_singleton_iff]

theorem physicalBlockOffset_injective (h : Nat) :
    Function.Injective (fun p : PhysicalPosition h => (physicalBlock h p, physicalOffset h p)) := by
  intro p q he
  have hb := congrArg Prod.fst he
  have ho := congrArg Prod.snd he
  rcases p with ⟨d, mode, group, offset⟩ | (⟨d, sign, position⟩ | (leaf | offset))
  · rcases q with ⟨d', mode', group', offset'⟩ | (⟨d', sign', position'⟩ | (leaf' | offset'))
    · have hb' := Block.anchor.inj hb
      have hd : d = d' := by
        apply Fin.ext
        have hm := congrArg Mode.depth hb'.1
        simp only [physicalBlock, mode_from_code_depth] at hm
        omega
      have hm : mode = mode' := by
        apply Fin.ext
        simpa only [physicalBlock, mode_code_of_code mode.val (d.val + 1) (by omega),
          mode_code_of_code mode'.val (d'.val + 1) (by omega)] using congrArg modeCode hb'.1
      have hg : group = group' := Fin.ext (by omega)
      have hf : offset = offset' := Fin.ext ho
      simp only [hd, hm, hg, hf]
    · simp [physicalBlock] at hb
    · simp [physicalBlock] at hb
    · simp [physicalBlock] at hb
  · rcases q with ⟨d', mode', group', offset'⟩ | (⟨d', sign', position'⟩ | (leaf' | offset'))
    · simp [physicalBlock] at hb
    · have hb' := Block.variable.inj hb
      have hd : d = d' := Fin.ext hb'.1
      subst d'
      have hs : sign = sign' := by
        fin_cases sign <;> fin_cases sign' <;> simp_all [physicalBlock]
      have hp : position = position' := by
        apply Fin.ext
        have hn := hb'.2.1
        change position.val / 2 ^ (h - d.val) = position'.val / 2 ^ (h - d.val) at hn
        change position.val % 2 ^ (h - d.val) = position'.val % 2 ^ (h - d.val) at ho
        calc
          position.val = position.val % 2 ^ (h - d.val) +
              2 ^ (h - d.val) * (position.val / 2 ^ (h - d.val)) :=
            (Nat.mod_add_div _ _).symm
          _ = position'.val % 2 ^ (h - d.val) +
              2 ^ (h - d.val) * (position'.val / 2 ^ (h - d.val)) := by rw [hn, ho]
          _ = position'.val := Nat.mod_add_div _ _
      simp only [hs, hp]
    · have hd := (Block.variable.inj hb).1
      have ht := d.isLt
      change d.val = h at hd
      omega
    · simp [physicalBlock] at hb
  · rcases q with ⟨d', mode', group', offset'⟩ | (⟨d', sign', position'⟩ | (leaf' | offset'))
    · simp [physicalBlock] at hb
    · have hd := (Block.variable.inj hb).1
      have ht := d'.isLt
      change h = d'.val at hd
      omega
    · have hl : leaf = leaf' := Fin.ext (Block.variable.inj hb).2.1
      simp only [hl]
    · simp [physicalBlock] at hb
  · rcases q with ⟨d', mode', group', offset'⟩ | (⟨d', sign', position'⟩ | (leaf' | offset'))
    · simp [physicalBlock] at hb
    · simp [physicalBlock] at hb
    · simp [physicalBlock] at hb
    · have hf : offset = offset' := Fin.ext ho
      simp only [hf]

def physicalOrderKey (h : Nat) (axis : Axis) (p : PhysicalPosition h) : List Nat ×ₗ Nat :=
  toLex (blockOrderKey axis (physicalBlock h p), physicalOffset h p)

theorem physicalOrderKey_injective (h : Nat) (axis : Axis) :
    Function.Injective (physicalOrderKey h axis) := by
  intro p q he
  have hp := Prod.mk.inj (congrArg ofLex he)
  have hb := (blockOrderKey_eq_iff h axis _ _
    (physicalBlock_valid h p) (physicalBlock_valid h q)).mp hp.1
  exact physicalBlockOffset_injective h (Prod.ext hb hp.2)

theorem physicalOrderKey_lt_iff (h : Nat) (axis : Axis) (p q : PhysicalPosition h) :
    physicalOrderKey h axis p < physicalOrderKey h axis q ↔
      physicalBefore h (axis == .row) p q := by
  rw [physicalOrderKey, physicalOrderKey, Prod.Lex.toLex_lt_toLex,
    blockOrderKey_lt_iff h axis _ _ (physicalBlock_valid h p) (physicalBlock_valid h q),
    blockOrderKey_eq_iff h axis _ _ (physicalBlock_valid h p) (physicalBlock_valid h q)]
  exact or_comm

abbrev PhysicalKeyRange (h : Nat) (axis : Axis) := Set.range (physicalOrderKey h axis)

noncomputable def physicalKeyEquiv (h : Nat) (axis : Axis) :
    PhysicalPosition h ≃ PhysicalKeyRange h axis :=
  Equiv.ofInjective (physicalOrderKey h axis) (physicalOrderKey_injective h axis)

noncomputable instance (h : Nat) (axis : Axis) : Fintype (PhysicalKeyRange h axis) :=
  Fintype.ofEquiv (PhysicalPosition h) (physicalKeyEquiv h axis)

noncomputable def orderedPhysicalKeys (h : Nat) (axis : Axis) :
    Fin (hostSideLength h) ≃o PhysicalKeyRange h axis :=
  monoEquivOfFin (PhysicalKeyRange h axis)
    ((Fintype.card_congr (physicalKeyEquiv h axis)).symm.trans (physicalPosition_card h))

noncomputable def physicalIndex (h : Nat) (axis : Axis) :
    Fin (hostSideLength h) ≃ PhysicalPosition h :=
  (orderedPhysicalKeys h axis).toEquiv.trans (physicalKeyEquiv h axis).symm

theorem physicalIndex_key (h : Nat) (axis : Axis) (i : Fin (hostSideLength h)) :
    physicalOrderKey h axis (physicalIndex h axis i) = (orderedPhysicalKeys h axis i).val := by
  exact congrArg Subtype.val ((physicalKeyEquiv h axis).apply_symm_apply _)

theorem physicalIndex_before (h : Nat) (axis : Axis) (i j : Fin (hostSideLength h)) :
    physicalBefore h (axis == .row) (physicalIndex h axis i) (physicalIndex h axis j) ↔ i < j := by
  rw [← physicalOrderKey_lt_iff h axis, physicalIndex_key, physicalIndex_key]
  exact (orderedPhysicalKeys h axis).lt_iff_lt

end H4Formal
