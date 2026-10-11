import H4Formal.ConcreteWordCompression

namespace H4Formal

def bitNat (b : Bool) : Nat := if b then 1 else 0

def wordNat : BinaryWord → Nat
  | [] => 0
  | b :: bs => bitNat b * 2 ^ bs.length + wordNat bs

theorem wordNat_lt (u : BinaryWord) : wordNat u < 2 ^ u.length := by
  induction u with
  | nil => simp [wordNat]
  | cons b bs ih =>
      cases b <;> simp [wordNat, bitNat, Nat.pow_succ] <;> omega

theorem wordNat_append (u v : BinaryWord) :
    wordNat (u ++ v) = wordNat u * 2 ^ v.length + wordNat v := by
  induction u with
  | nil => simp [wordNat]
  | cons b bs ih =>
      simp only [List.cons_append, wordNat, List.length_append, ih,
        Nat.pow_add, Nat.add_mul, Nat.mul_assoc]
      omega

theorem wordNat_concat (u : BinaryWord) (b : Bool) :
    wordNat (u ++ [b]) = wordNat u * 2 + bitNat b := by
  simp [wordNat_append, wordNat, bitNat]

theorem wordNat_injective_sameLength {u v : BinaryWord}
    (hlen : u.length = v.length) (hn : wordNat u = wordNat v) : u = v := by
  induction u generalizing v with
  | nil =>
      exact (List.length_eq_zero_iff.mp (by simpa using hlen.symm)).symm
  | cons b bs ih =>
      cases v with
      | nil => simp at hlen
      | cons c cs =>
          have hl : bs.length = cs.length := by simpa using hlen
          have hbs := wordNat_lt bs
          have hcs := wordNat_lt cs
          rw [hl] at hbs
          have hbc : b = c := by
            cases b <;> cases c <;> simp [wordNat, bitNat, hl] at hn ⊢ <;> omega
          subst c
          have he : wordNat bs = wordNat cs := by
            simp only [wordNat, hl] at hn
            omega
          rw [ih hl he]

theorem wordNat_lt_iff_lex {u v : BinaryWord} (hlen : u.length = v.length) :
    wordNat u < wordNat v ↔ binaryLexLess u v := by
  induction u generalizing v with
  | nil =>
      have hv : v = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst v
      simp [wordNat, binaryLexLess]
  | cons b bs ih =>
      cases v with
      | nil => simp at hlen
      | cons c cs =>
          have hl : bs.length = cs.length := by simpa using hlen
          have hbs := wordNat_lt bs
          have hcs := wordNat_lt cs
          have ht := ih hl
          cases b <;> cases c <;>
            simp [wordNat, bitNat, hl, binaryLexLess, List.cons_lex_cons_iff, bitLT] at * <;> omega

def wordLE (u v : BinaryWord) : Prop := u = v ∨ binaryLexLess u v

theorem wordNat_le_iff {u v : BinaryWord} (hlen : u.length = v.length) :
    wordNat u ≤ wordNat v ↔ wordLE u v := by
  constructor
  · intro h
    rcases Nat.eq_or_lt_of_le h with he | hl
    · exact Or.inl (wordNat_injective_sameLength hlen he)
    · exact Or.inr ((wordNat_lt_iff_lex hlen).mp hl)
  · intro h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_of_lt ((wordNat_lt_iff_lex hlen).mpr h)

theorem wordNat_parent (u : BinaryWord) :
    wordNat (parentWord u) = wordNat u / 2 := by
  rcases List.eq_nil_or_concat u with rfl | ⟨pre, b, rfl⟩
  · rfl
  · simp only [List.concat_eq_append, parentWord, List.dropLast_concat,
      wordNat_concat]
    cases b <;> simp [bitNat, Nat.add_div, Nat.mul_div_left]

def endpointNat (u : BinaryWord) : Nat := (endpointBit u).map bitNat |>.getD 0

theorem wordNat_parity (u : BinaryWord) : wordNat u % 2 = endpointNat u := by
  rcases List.eq_nil_or_concat u with rfl | ⟨pre, b, rfl⟩
  · rfl
  · cases b <;> simp [List.concat_eq_append, wordNat_concat, endpointNat,
      endpointBit, Nat.add_mod, bitNat]

def natWord : Nat → Nat → BinaryWord
  | 0, _ => []
  | d + 1, p => natWord d (p / 2) ++ [decide (p % 2 = 1)]

@[simp] theorem natWord_length (d p : Nat) : (natWord d p).length = d := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => simp [natWord, ih]

theorem wordNat_natWord (d p : Nat) (hp : p < 2 ^ d) :
    wordNat (natWord d p) = p := by
  induction d generalizing p with
  | zero => have : p = 0 := by simpa using hp
            subst p
            rfl
  | succ d ih =>
      have hp' : p / 2 < 2 ^ d := by
        have hp'' : p < 2 ^ d * 2 := by simpa [Nat.pow_succ] using hp
        omega
      rw [natWord, wordNat_concat, ih (p / 2) hp']
      have hr := Nat.mod_lt p (by decide : 0 < 2)
      have hm := Nat.mod_add_div p 2
      by_cases he : p % 2 = 1
      · simp [bitNat, he]
        omega
      · have hz : p % 2 = 0 := by omega
        simp [bitNat, he]
        omega

theorem natWord_wordNat (u : BinaryWord) : natWord u.length (wordNat u) = u := by
  apply wordNat_injective_sameLength
  · simp
  · exact wordNat_natWord u.length (wordNat u) (wordNat_lt u)

theorem wordNat_prefix_quotient {u v : BinaryWord} (h : u <+: v) :
    wordNat u = wordNat v / 2 ^ (v.length - u.length) := by
  rcases h with ⟨tail, rfl⟩
  rw [wordNat_append]
  simp only [List.length_append, Nat.add_sub_cancel_left]
  have hpow := Nat.two_pow_pos tail.length
  have ht := wordNat_lt tail
  rw [Nat.mul_comm (wordNat u), Nat.mul_add_div hpow,
    Nat.div_eq_of_lt ht, Nat.add_zero]

theorem wordNat_prefix_iff {u v : BinaryWord} (hlen : u.length ≤ v.length) :
    u <+: v ↔ wordNat u = wordNat v / 2 ^ (v.length - u.length) := by
  constructor
  · exact wordNat_prefix_quotient
  · intro he
    have ht : (v.take u.length).length = u.length := by
      simp [List.length_take, Nat.min_eq_left hlen]
    have hp := List.take_prefix u.length v
    have hq := wordNat_prefix_quotient hp
    rw [ht] at hq
    have he' : wordNat u = wordNat (v.take u.length) := by
      simpa [ht] using he.trans hq.symm
    have hu := wordNat_injective_sameLength ht.symm he'
    rw [hu]
    exact hp

theorem lex_iff_prefix_numeric_lt {u v : BinaryWord} (hlen : u.length ≤ v.length)
    (hprefix : ¬ u <+: v) :
    binaryLexLess u v ↔ wordNat u < wordNat v / 2 ^ (v.length - u.length) := by
  have hlex : binaryLexLess u v ↔ binaryLexLess u (v.take u.length) := by
    induction u generalizing v with
    | nil => simp at hprefix
    | cons b bs ih =>
        cases v with
        | nil => simp at hlen
        | cons c cs =>
            have hl : bs.length ≤ cs.length := by simpa using hlen
            by_cases he : b = c
            · subst c
              have hn : ¬ bs <+: cs := by simpa using hprefix
              simpa [binaryLexLess, List.cons_lex_cons_iff] using ih hl hn
            · simp [binaryLexLess, List.cons_lex_cons_iff, he]
  have ht : (v.take u.length).length = u.length := by
    simp [List.length_take, Nat.min_eq_left hlen]
  have hq := wordNat_prefix_quotient (List.take_prefix u.length v)
  rw [ht] at hq
  rw [← hq, wordNat_lt_iff_lex ht.symm]
  exact hlex

theorem lex_iff_prefix_numeric_lt_left {u v : BinaryWord}
    (hlen : v.length ≤ u.length) (hprefix : ¬ v <+: u) :
    binaryLexLess u v ↔ wordNat u / 2 ^ (u.length - v.length) < wordNat v := by
  have hlex : binaryLexLess u v ↔ binaryLexLess (u.take v.length) v := by
    induction v generalizing u with
    | nil => simp at hprefix
    | cons c cs ih =>
        cases u with
        | nil => simp at hlen
        | cons b bs =>
            have hl : cs.length ≤ bs.length := by simpa using hlen
            by_cases he : b = c
            · subst b
              have hn : ¬ cs <+: bs := by simpa using hprefix
              simpa [binaryLexLess, List.cons_lex_cons_iff] using ih hl hn
            · simp [binaryLexLess, List.cons_lex_cons_iff, he]
  have ht : (u.take v.length).length = v.length := by
    simp [List.length_take, Nat.min_eq_left hlen]
  have hq := wordNat_prefix_quotient (List.take_prefix v.length u)
  rw [ht] at hq
  rw [← hq, wordNat_lt_iff_lex ht]
  exact hlex

theorem SelectedWordCompressionWitness.numeric_lt_iff
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support)
    (hl : u.length = v.length) :
    wordNat (w.map u) < wordNat (w.map v) ↔ wordNat u < wordNat v := by
  have hl' : (w.map u).length = (w.map v).length := by
    rw [w.length_map _ hu, w.length_map _ hv, hl]
  rw [wordNat_lt_iff_lex hl', wordNat_lt_iff_lex hl, w.lex_iff hu hv]

theorem SelectedWordCompressionWitness.numeric_le_iff
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support)
    (hl : u.length = v.length) :
    wordNat (w.map u) ≤ wordNat (w.map v) ↔ wordNat u ≤ wordNat v := by
  have hl' : (w.map u).length = (w.map v).length := by
    rw [w.length_map _ hu, w.length_map _ hv, hl]
  rw [wordNat_le_iff hl', wordNat_le_iff hl]
  simp only [wordLE, w.map_eq_iff hu hv, w.lex_iff hu hv]

end H4Formal
