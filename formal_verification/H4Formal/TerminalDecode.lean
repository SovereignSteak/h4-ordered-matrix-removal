import H4Formal.ArithmeticHost
import H4Formal.CopyFibres

namespace H4Formal
open Arithmetic

theorem decode_variable (b : Block) (hk : (encode b).kind = 1) :
    ∃ d p s, b = .variable d p s := by
  cases b with
  | anchor m g => simp [encode] at hk
  | dummy => simp [encode] at hk
  | «variable» d p s => exact ⟨d, p, s, rfl⟩

theorem decode_dummy (b : Block) (hk : (encode b).kind = 2) : b = .dummy := by
  cases b <;> simp [encode] at hk ⊢

theorem decode_leaf (h : Nat) (b : Block) (hb : ValidBlock h b)
    (hk : (encode b).kind = 1) (hd : (encode b).depth = h) :
    ∃ p, p < 2 ^ h ∧ b = .variable h p .leaf := by
  obtain ⟨d, p, s, rfl⟩ := decode_variable b hk
  have hdh : d = h := by simp only [encode] at hd; omega
  subst d
  have hs : s = .leaf := by simpa [ValidBlock] using hb.2.2
  subst s
  exact ⟨p, hb.2.1, rfl⟩

theorem decode_anchor (h : Nat) (b : Block) (hb : ValidBlock h b)
    (m : Mode) (hm : ValidMode h m) (g : Nat)
    (hk : (encode b).kind = 0) (hn : (encode b).mode = modeNumber m)
    (hd : (encode b).level = m.depth) (hg : (encode b).group = g) : b = .anchor m g := by
  cases b with
  | dummy => simp [encode] at hk
  | «variable» d p s => simp [encode] at hk
  | anchor n k =>
      have hnum : modeNumber n = modeNumber m := by simp only [encode] at hn; omega
      have hdepth : n.depth = m.depth := by simp only [encode] at hd; omega
      have hgroup : k = g := by simp only [encode] at hg; omega
      have hmode := (mode_eq_iff_encoded h n m hb.1 hm).2 ⟨hnum, hdepth⟩
      subst n; subst k
      rfl

theorem leaf_marker_mode (h p : Nat) (a : Pos)
    (hk : a.kind = 0) (hm : a.mode = 4 ∨ a.mode = 5)
    (hl : a.level = h) (hg : a.group = 1)
    (he : entry false h (encode (.variable h p .leaf)) a) :
    a.mode = modeNumber (terminalMode h p) := by
  rcases hm with hm4 | hm5
  · have hpar : (p : Int) % 2 = 0 := by
      simpa [entry, signature, atSign, atParity, pIf, encode, encodeSign,
        hk, hm4, hg, hl] using he
    have hpar' : p % 2 = 0 := by omega
    simpa [terminalMode, modeNumber, hpar'] using hm4
  · have hpar : (p : Int) % 2 = 1 := by
      simpa [entry, signature, atSign, atParity, pIf, encode, encodeSign,
        hk, hm5, hg, hl] using he
    have hpar' : p % 2 = 1 := by omega
    simpa [terminalMode, modeNumber, hpar'] using hm5

/-- Decode terminal forms and recover marker parity from the copy entries. -/
theorem terminal_decodes (h : Nat) (hh : 1 ≤ h) (r c : Fin 4 → Block)
    (hc : ValidCopy h (originalHost h) r c)
    (ht : terminal h (encode (r 0)) (encode (r 1)) (encode (r 2)) (encode (r 3))
      (encode (c 0)) (encode (c 1)) (encode (c 2)) (encode (c 3))) :
    ∃ p, p < 2 ^ h ∧ r = terminalRows h p ∧
      (c = terminalIColumns h p ∨
        ∃ q, q < p ∧ q % 2 = p % 2 ∧ c = terminalIIColumns h p q) := by
  rcases ht with ⟨hr0k, hr1k, hc0k, hm0, hm01, hm00, hr0l, hr1l, hc0l,
    hr0g, hr1g, hc0g, hr2k, hr2d, hr3k, hc2k, hc2d, hnodes,
    hc3k, hc3d, hc3s, hc3node, hchoice⟩
  obtain ⟨p, hp, hr2⟩ := decode_leaf h (r 2) (hc.1 2) hr2k hr2d
  obtain ⟨v, _, hc2⟩ := decode_leaf h (c 2) (hc.2.1 2) hc2k hc2d
  have hv : v = p := by simp only [hr2, hc2, encode] at hnodes; omega
  subst v
  have hr3 := decode_dummy (r 3) hr3k
  have ha := encode_copy h false r c (by simpa only [quotientHost] using hc)
  have he : entry false h (encode (r 2)) (encode (c 0)) :=
    (ha.2.2.2.2 (2 : Fin 4) (0 : Fin 4)).mpr (by decide)
  have hc0mode : (encode (c 0)).mode = modeNumber (terminalMode h p) :=
    leaf_marker_mode h p (encode (c 0)) hc0k (by simpa only [hm00] using hm0)
      hc0l hc0g (by simpa only [hr2] using he)
  have hmode := hm00.trans hc0mode
  have hm := terminalMode_valid h p hh
  have hr0 := decode_anchor h (r 0) (hc.1 0) (terminalMode h p) hm 1
    hr0k hmode hr0l hr0g
  have hr1 := decode_anchor h (r 1) (hc.1 1) (terminalMode h p) hm 2
    hr1k (hm01.symm.trans hmode) hr1l hr1g
  have hc0 := decode_anchor h (c 0) (hc.2.1 0) (terminalMode h p) hm 1
    hc0k (hm00.symm.trans hmode) hc0l hc0g
  obtain ⟨d, v, s, hc3⟩ := decode_variable (c 3) hc3k
  have hd : d = h - 1 := by simp only [hc3, encode] at hc3d; omega
  have hv : v = p / 2 := by simp only [hc3, hr2, encode] at hc3node; omega
  have hs : s = .minus := by
    cases s <;> simp [hc3, encode, encodeSign] at hc3s ⊢
  subst d; subst v; subst s
  have hrows : r = terminalRows h p := by
    rw [← four_eta r]
    simp only [hr0, hr1, hr2, hr3, terminalRows]
  refine ⟨p, hp, hrows, ?_⟩
  rcases hchoice with ⟨hc1k, hc1mode, hc1level, hc1group⟩ | ⟨hc1k, hc1depth, hqp, hpar⟩
  · have hc1 := decode_anchor h (c 1) (hc.2.1 1) (terminalMode h p) hm 2
      hc1k (hc1mode.trans hmode) hc1level hc1group
    left
    rw [← four_eta c]
    simp only [hc0, hc1, hc2, hc3, terminalIColumns]
  · obtain ⟨q, _, hc1⟩ := decode_leaf h (c 1) (hc.2.1 1) hc1k hc1depth
    have hqp' : q < p := by simp only [hc1, hr2, encode] at hqp; omega
    have hpar' : q % 2 = p % 2 := by simp only [hc1, hr2, encode] at hpar; omega
    right
    refine ⟨q, hqp', hpar', ?_⟩
    rw [← four_eta c]
    simp only [hc0, hc1, hc2, hc3, terminalIIColumns]

end H4Formal
