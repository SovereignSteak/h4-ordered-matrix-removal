import H4Formal.HostCompression
import H4Formal.Transfer

namespace H4Formal

theorem hostVariableBefore_words (axis : Axis) (u v : BinaryWord) (rs cs : Sign) :
    hostVariableBefore (axis == .row) u.length (wordNat u) rs
        v.length (wordNat v) cs = true ↔
      variableBefore axis ⟨u, rs⟩ ⟨v, cs⟩ := by
  by_cases hl : u.length = v.length
  · by_cases he : u = v
    · subst v
      cases axis <;> cases rs <;> cases cs <;>
        simp [hostVariableBefore, variableBefore, sameDepthSignBefore, signCode] <;> decide
    · have hn : wordNat u ≠ wordNat v := fun h => he (wordNat_injective_sameLength hl h)
      have hp : ¬ u <+: v := fun h => he (h.eq_of_length hl)
      have hq : ¬ v <+: u := fun h => he (h.eq_of_length hl.symm).symm
      simpa [hostVariableBefore, variableBefore, hl, hn, hp, hq] using
        wordNat_lt_iff_lex hl
  · by_cases hlt : u.length < v.length
    · have hq : ¬ v <+: u := fun h => by have := h.length_le; omega
      by_cases hp : u <+: v
      · have hn := wordNat_prefix_quotient hp
        cases axis <;> cases rs <;>
          simp [hostVariableBefore, variableBefore, hl, hlt, hp, hq, hn,
            ancestorSignBefore, signCode] <;> decide
      · have hn : wordNat u ≠ wordNat v / 2 ^ (v.length - u.length) :=
          fun h => hp ((wordNat_prefix_iff (Nat.le_of_lt hlt)).mpr h)
        simpa [hostVariableBefore, variableBefore, hl, hlt, hp, hq, hn] using
          (lex_iff_prefix_numeric_lt (Nat.le_of_lt hlt) hp).symm
    · have hle : v.length ≤ u.length := by omega
      have hp : ¬ u <+: v := fun h => by have := h.length_le; omega
      by_cases hq : v <+: u
      · have hn := wordNat_prefix_quotient hq
        cases axis <;> cases cs <;>
          simp [hostVariableBefore, variableBefore, hl, hlt, hp, hq, hn,
            descendantSignBefore, signCode] <;> decide
      · have hn : wordNat v ≠ wordNat u / 2 ^ (u.length - v.length) :=
          fun h => hq ((wordNat_prefix_iff hle).mpr h)
        simpa [hostVariableBefore, variableBefore, hl, hlt, hp, hq, hn] using
          (lex_iff_prefix_numeric_lt_left hle hq).symm

theorem hostVariableBefore_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true)
    {rd rp cd cp : Nat} {rs cs : Sign}
    (hr : Block.variable rd rp rs ∈ selected)
    (hc : Block.variable cd cp cs ∈ selected) (axis : Axis) :
    hostVariableBefore (axis == .row)
        (retainedDepth (compressionLevels h selected) rd)
        (compressedNode (compressionLevels h selected) rd rp) rs
        (retainedDepth (compressionLevels h selected) cd)
        (compressedNode (compressionLevels h selected) cd cp) cs =
      hostVariableBefore (axis == .row) rd rp rs cd cp cs := by
  let w := blockWordWitness h selected hv
  have hu := variable_word_mem_support hr
  have hv' := variable_word_mem_support hc
  have hrp : rp < 2 ^ rd := by
    have hh := hv _ hr
    simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  have hcp : cp < 2 ^ cd := by
    have hh := hv _ hc
    simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  have hleft := hostVariableBefore_words axis (w.map (natWord rd rp))
    (w.map (natWord cd cp)) rs cs
  have hright := hostVariableBefore_words axis (natWord rd rp) (natWord cd cp) rs cs
  have hpres := variableBefore_preserved w axis
    ⟨natWord rd rp, rs⟩ ⟨natWord cd cp, cs⟩ hu hv'
  rw [w.length_map _ hu, w.length_map _ hv'] at hleft
  simp only [natWord_length] at hleft
  simp only [natWord_length, wordNat_natWord _ _ hrp,
    wordNat_natWord _ _ hcp] at hright
  change (hostVariableBefore (axis == .row)
    (retainedDepth (compressionLevels h selected) rd)
    (compressedNode (compressionLevels h selected) rd rp) rs
    (retainedDepth (compressionLevels h selected) cd)
    (compressedNode (compressionLevels h selected) cd cp) cs = true ↔ _) at hleft
  have he : _ = true ↔ _ = true := hleft.trans (hpres.trans hright.symm)
  cases h1 : hostVariableBefore (axis == .row)
      (retainedDepth (compressionLevels h selected) rd)
      (compressedNode (compressionLevels h selected) rd rp) rs
      (retainedDepth (compressionLevels h selected) cd)
      (compressedNode (compressionLevels h selected) cd cp) cs <;>
    cases h2 : hostVariableBefore (axis == .row) rd rp rs cd cp cs <;>
    simp_all

theorem hostModeBefore_compress (levels : List Nat) (xm ym : Mode) (xg yg : Nat)
    (hx : xm.depth ∈ levels) (hy : ym.depth ∈ levels) (minusFirst : Bool) :
    hostModeBefore minusFirst (compressMode levels xm) (compressMode levels ym) xg yg =
      hostModeBefore minusFirst xm ym xg yg := by
  have he := projectCount_eq_iff_of_mem levels hx hy
  have hl := projectCount_lt_iff_of_mem levels hx hy
  change (retainedDepth levels xm.depth = retainedDepth levels ym.depth ↔ _) at he
  change (retainedDepth levels xm.depth < retainedDepth levels ym.depth ↔ _) at hl
  simp only [hostModeBefore, modeCode_compress]
  simp [compressMode, he, hl]

theorem hostComesBefore_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) {r c : Block}
    (hr : r ∈ selected) (hc : c ∈ selected) (minusFirst isRow : Bool) :
    hostComesBefore minusFirst isRow
        (compressBlock (compressionLevels h selected) r)
        (compressBlock (compressionLevels h selected) c) =
      hostComesBefore minusFirst isRow r c := by
  cases r with
  | anchor rm rg =>
      cases c with
      | anchor cm cg =>
          exact hostModeBefore_compress _ rm cm rg cg
            (defining_mem_compressionLevels h selected (blockLevels_mem_anchor hr))
            (defining_mem_compressionLevels h selected (blockLevels_mem_anchor hc)) minusFirst
      | «variable» _ _ _ => rfl
      | dummy => rfl
  | «variable» rd rp rs =>
      cases c with
      | anchor _ _ => rfl
      | «variable» cd cp cs =>
          cases isRow
          · exact hostVariableBefore_compress h selected hv hr hc .column
          · exact hostVariableBefore_compress h selected hv hr hc .row
      | dummy => rfl
  | dummy => cases c <;> rfl

def concreteHost (h : Nat) (repair : Bool) : OrderedBlockHost where
  value := if repair then repairedValue h else hostValue h
  rowBefore r s := hostComesBefore true true r s = true
  colBefore c d := hostComesBefore true false c d = true

def selectedRecords (rows cols : Fin 4 → Block) : List Block :=
  List.ofFn rows ++ List.ofFn cols

@[simp] theorem selectedRecords_length (rows cols : Fin 4 → Block) :
    (selectedRecords rows cols).length = 8 := by simp [selectedRecords]

theorem row_mem_selectedRecords (rows cols : Fin 4 → Block) (i : Fin 4) :
    rows i ∈ selectedRecords rows cols :=
  List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem col_mem_selectedRecords (rows cols : Fin 4 → Block) (i : Fin 4) :
    cols i ∈ selectedRecords rows cols :=
  List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

def IsValidCopy (h : Nat) (repair : Bool) (rows cols : Fin 4 → Block) : Prop :=
  (∀ b ∈ selectedRecords rows cols, validBlock h b = true) ∧
    IsCopy (concreteHost h repair) rows cols

theorem compressionDepth_bounds (h : Nat) (rows cols : Fin 4 → Block) (hh : 0 < h) :
    let k := retainedDepth (compressionLevels h (selectedRecords rows cols)) h
    1 ≤ k ∧ k ≤ 24 := by
  dsimp
  constructor
  · exact actualRetainedDepth_pos h _ _ hh
  · apply actualRetainedDepth_le_24
    · exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)
    · exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem isValidCopy_compress (h : Nat) (repair : Bool) (rows cols : Fin 4 → Block)
    (hc : IsValidCopy h repair rows cols) :
    let levels := compressionLevels h (selectedRecords rows cols)
    IsValidCopy (retainedDepth levels h) repair
      (fun i => compressBlock levels (rows i))
      (fun i => compressBlock levels (cols i)) := by
  let selected := selectedRecords rows cols
  let levels := compressionLevels h selected
  have hv : ∀ b ∈ selected, validBlock h b = true := hc.1
  constructor
  · intro b hb
    simp only [selectedRecords, List.mem_append, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact validBlock_compress h selected hv (row_mem_selectedRecords rows cols i)
    · exact validBlock_compress h selected hv (col_mem_selectedRecords rows cols i)
  constructor
  · intro i j hij
    change hostComesBefore true true _ _ = true
    rw [hostComesBefore_compress h selected hv
      (row_mem_selectedRecords rows cols i) (row_mem_selectedRecords rows cols j)]
    exact hc.2.1 i j hij
  constructor
  · intro i j hij
    change hostComesBefore true false _ _ = true
    rw [hostComesBefore_compress h selected hv
      (col_mem_selectedRecords rows cols i) (col_mem_selectedRecords rows cols j)]
    exact hc.2.2.1 i j hij
  · intro i j
    have hr := row_mem_selectedRecords rows cols i
    have hcol := col_mem_selectedRecords rows cols j
    have he := hc.2.2.2 i j
    cases repair
    · change hostValue (retainedDepth levels h)
        (compressBlock levels (rows i)) (compressBlock levels (cols j)) = pattern i j
      rw [hostValue_compress h selected hv hr hcol]
      exact he
    · change repairedValue (retainedDepth levels h)
        (compressBlock levels (rows i)) (compressBlock levels (cols j)) = pattern i j
      rw [repairedValue_compress h selected hv hr hcol]
      exact he

theorem copy_has_small_witness (h : Nat) (repair : Bool) (hh : 0 < h)
    (rows cols : Fin 4 → Block) (hc : IsValidCopy h repair rows cols) :
    ∃ k, 1 ≤ k ∧ k ≤ 24 ∧ ∃ rows' cols', IsValidCopy k repair rows' cols' := by
  let levels := compressionLevels h (selectedRecords rows cols)
  exact ⟨retainedDepth levels h, (compressionDepth_bounds h rows cols hh).1,
    (compressionDepth_bounds h rows cols hh).2,
    (fun i => compressBlock levels (rows i)),
    (fun i => compressBlock levels (cols i)), isValidCopy_compress h repair rows cols hc⟩

end H4Formal
