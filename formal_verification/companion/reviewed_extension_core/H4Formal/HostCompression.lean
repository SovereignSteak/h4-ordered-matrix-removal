import H4Formal.ActualRetention
import H4Formal.BinaryWords
import H4Formal.EncodedSemantics

namespace H4Formal

def blockLevels (selected : List Block) : List Nat :=
  selected.filterMap (fun b => match b with
    | .anchor m _ => some m.depth
    | .variable d _ _ => some d
    | .dummy => none)

def blockWords (selected : List Block) : List BinaryWord :=
  selected.filterMap (fun b => match b with
    | .variable d p _ => some (natWord d p)
    | _ => none)

def compressionLevels (h : Nat) (selected : List Block) : List Nat :=
  actualRetainedLevels h (blockLevels selected) (blockWords selected)

def compressMode (levels : List Nat) (m : Mode) : Mode :=
  { m with depth := retainedDepth levels m.depth }

def compressedNode (levels : List Nat) (d p : Nat) : Nat :=
  wordNat (projectWord levels (natWord d p))

def compressBlock (levels : List Nat) : Block → Block
  | .anchor m g => .anchor (compressMode levels m) g
  | .variable d p s => .variable (retainedDepth levels d) (compressedNode levels d p) s
  | .dummy => .dummy

@[simp] theorem compressBlock_dummy_iff (levels : List Nat) (b : Block) :
    compressBlock levels b = .dummy ↔ b = .dummy := by
  cases b <;> simp [compressBlock]

theorem blockLevels_mem_anchor {selected : List Block} {m : Mode} {g : Nat}
    (hb : Block.anchor m g ∈ selected) : m.depth ∈ blockLevels selected := by
  exact List.mem_filterMap.mpr ⟨.anchor m g, hb, rfl⟩

theorem blockLevels_mem_variable {selected : List Block} {d p : Nat} {s : Sign}
    (hb : Block.variable d p s ∈ selected) : d ∈ blockLevels selected := by
  exact List.mem_filterMap.mpr ⟨.variable d p s, hb, rfl⟩

theorem blockWords_mem_variable {selected : List Block} {d p : Nat} {s : Sign}
    (hb : Block.variable d p s ∈ selected) : natWord d p ∈ blockWords selected := by
  exact List.mem_filterMap.mpr ⟨.variable d p s, hb, rfl⟩

theorem defining_mem_compressionLevels (h : Nat) (selected : List Block) {d : Nat}
    (hd : d ∈ blockLevels selected) : d ∈ compressionLevels h selected :=
  actualRetainedLevels_mem h _ _ (Or.inr (Or.inr (Or.inl hd)))

theorem predecessor_mem_compressionLevels (h : Nat) (selected : List Block)
    {d : Nat} (hd : d ∈ blockLevels selected) : d - 1 ∈ compressionLevels h selected := by
  by_cases hz : d = 0
  · subst d
    exact actualRetainedLevels_mem h _ _ (Or.inl rfl)
  · apply actualRetainedLevels_mem
    right; right; right; left
    exact List.mem_filterMap.mpr ⟨d, hd, by simp [hz]⟩

theorem endpoint_mem_compressionLevels (h : Nat) (selected : List Block) :
    h ∈ compressionLevels h selected :=
  actualRetainedLevels_mem h _ _ (Or.inr (Or.inl rfl))

theorem blockWords_lengths (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) :
    ∀ u ∈ blockWords selected, u.length ≤ h := by
  intro u hu
  rcases List.mem_filterMap.mp hu with ⟨b, hb, he⟩
  cases b with
  | anchor m g => simp [blockWords] at he
  | dummy => simp [blockWords] at he
  | «variable» d p s =>
      simp at he
      subst u
      have hh := hv _ hb
      simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
      simpa using hh.1.1

theorem blockWords_defining (selected : List Block) :
    ∀ u ∈ blockWords selected, u.length ∈ blockLevels selected := by
  intro u hu
  rcases List.mem_filterMap.mp hu with ⟨b, hb, he⟩
  cases b with
  | anchor m g => simp [blockWords] at he
  | dummy => simp [blockWords] at he
  | «variable» d p s =>
      simp at he
      subst u
      simpa using blockLevels_mem_variable hb

def blockWordWitness (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) :
    SelectedWordCompressionWitness (parentSupport (blockWords selected)) :=
  actualParentProjectedWitness h (blockLevels selected) (blockWords selected)
    (blockWords_lengths h selected hv) (blockWords_defining selected)

theorem blockWordWitness_map (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) (u : BinaryWord) :
    (blockWordWitness h selected hv).map u = projectWord (compressionLevels h selected) u := rfl

theorem variable_word_mem_support {selected : List Block} {d p : Nat} {s : Sign}
    (hb : Block.variable d p s ∈ selected) :
    natWord d p ∈ parentSupport (blockWords selected) := by
  exact List.mem_append_left _ (blockWords_mem_variable hb)

theorem variable_parent_mem_support {selected : List Block} {d p : Nat} {s : Sign}
    (hb : Block.variable d p s ∈ selected) :
    parentWord (natWord d p) ∈ parentSupport (blockWords selected) := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨_, blockWords_mem_variable hb, rfl⟩)

theorem compressedNode_parity (levels : List Nat) (d p : Nat)
    (hd : d ∈ levels) (hp : p < 2 ^ d) : compressedNode levels d p % 2 = p % 2 := by
  rw [compressedNode, wordNat_parity, endpointNat,
    projectWord_endpoint levels _ (by simpa using hd)]
  rw [← endpointNat, ← wordNat_parity, wordNat_natWord d p hp]

theorem compressedNode_compare (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true)
    {i p j q : Nat} {rs cs : Sign}
    (hr : Block.variable i p rs ∈ selected) (hc : Block.variable j q cs ∈ selected)
    (he : i = j) :
    (compressedNode (compressionLevels h selected) i p < compressedNode (compressionLevels h selected) j q ↔ p < q) ∧
    (compressedNode (compressionLevels h selected) i p ≤ compressedNode (compressionLevels h selected) j q ↔ p ≤ q) := by
  have hp : p < 2 ^ i := by
    have hh := hv _ hr
    simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  have hq : q < 2 ^ j := by
    have hh := hv _ hc
    simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  let w := blockWordWitness h selected hv
  have hlu : (natWord i p).length = (natWord j q).length := by simpa using he
  have hl := w.numeric_lt_iff (variable_word_mem_support hr) (variable_word_mem_support hc) hlu
  have hle := w.numeric_le_iff (variable_word_mem_support hr) (variable_word_mem_support hc) hlu
  simpa [w, blockWordWitness_map, compressedNode, wordNat_natWord i p hp,
    wordNat_natWord j q hq] using And.intro hl hle

theorem compressedNode_parent_compare (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true)
    {i p j q : Nat} {rs cs : Sign}
    (hr : Block.variable i p rs ∈ selected) (hc : Block.variable j q cs ∈ selected)
    (he : i = j + 1) :
    (compressedNode (compressionLevels h selected) i p / 2 < compressedNode (compressionLevels h selected) j q ↔ p / 2 < q) ∧
    (compressedNode (compressionLevels h selected) i p / 2 ≤ compressedNode (compressionLevels h selected) j q ↔ p / 2 ≤ q) := by
  have hp : p < 2 ^ i := by
    have hh := hv _ hr
    simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  have hq : q < 2 ^ j := by
    have hh := hv _ hc
    simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.2
  let w := blockWordWitness h selected hv
  have hlu : (parentWord (natWord i p)).length = (natWord j q).length := by
    simp [parentWord, List.length_dropLast, he]
  have hl := w.numeric_lt_iff (variable_parent_mem_support hr) (variable_word_mem_support hc) hlu
  have hle := w.numeric_le_iff (variable_parent_mem_support hr) (variable_word_mem_support hc) hlu
  have hpa := w.parent_iff (variable_word_mem_support hr)
  rw [← hpa, wordNat_parent, wordNat_parent,
    wordNat_natWord i p hp, wordNat_natWord j q hq] at hl hle
  simpa [w, blockWordWitness_map, compressedNode] using And.intro hl hle

@[simp] theorem allowedMode_compress (levels : List Nat) (m : Mode) :
    allowedMode (compressMode levels m) = allowedMode m := by
  cases m
  rfl

@[simp] theorem modeCode_compress (levels : List Nat) (m : Mode) :
    modeCode (compressMode levels m) = modeCode m := by
  cases m with
  | mk family depth parity sign =>
      cases family <;> cases sign <;> simp [compressMode, modeCode]
      all_goals cases parity with
        | zero => rfl
        | succ p => cases p <;> rfl

theorem compressMode_eq_iff (levels : List Nat) (m n : Mode)
    (hm : m.depth ∈ levels) (hn : n.depth ∈ levels) :
    compressMode levels m = compressMode levels n ↔ m = n := by
  have he := projectCount_eq_iff_of_mem levels hm hn
  change (retainedDepth levels m.depth = retainedDepth levels n.depth ↔ m.depth = n.depth) at he
  cases m
  cases n
  simp only [compressMode, Mode.mk.injEq, he]

theorem compressedNode_lt_bound (levels : List Nat) (d p : Nat) :
    compressedNode levels d p < 2 ^ retainedDepth levels d := by
  simpa [compressedNode, projectWord_length] using wordNat_lt (projectWord levels (natWord d p))

theorem validBlock_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) {b : Block} (hb : b ∈ selected) :
    validBlock (retainedDepth (compressionLevels h selected) h)
      (compressBlock (compressionLevels h selected) b) = true := by
  let levels := compressionLevels h selected
  have hvalid := hv b hb
  cases b with
  | dummy => rfl
  | anchor m g =>
      have hm := defining_mem_compressionLevels h selected (blockLevels_mem_anchor hb)
      simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq,
        Bool.or_eq_true, beq_iff_eq] at hvalid
      have hpos : 0 < retainedDepth levels m.depth := by
        have hp : 0 < m.depth := by have := hvalid.1.1.1; omega
        exact projectCount_pos_of_mem levels 0 m.depth hp (by simpa using hm)
      have hmd : m.depth ≤ h := hvalid.1.1.2
      have hle := retainedDepth_mono levels hmd
      dsimp only [levels] at *
      simp only [validBlock, compressBlock, allowedMode_compress, compressMode,
        Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨⟨by omega, hle⟩, hvalid.1.2⟩, hvalid.2⟩
  | «variable» d p s =>
      have hd := defining_mem_compressionLevels h selected (blockLevels_mem_variable hb)
      have hh := endpoint_mem_compressionLevels h selected
      have he := projectCount_eq_iff_of_mem levels hd hh
      change (retainedDepth levels d = retainedDepth levels h ↔ d = h) at he
      dsimp only [levels] at *
      simp only [validBlock, compressBlock, Bool.and_eq_true, decide_eq_true_eq,
        he] at hvalid ⊢
      exact ⟨⟨retainedDepth_mono levels hvalid.1.1, compressedNode_lt_bound levels d p⟩,
        hvalid.2⟩

theorem matchesBlock_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) {b : Block} (hb : b ∈ selected)
    (d : Nat) (hd : d ∈ compressionLevels h selected) (s : Sign) (par : Option Nat) :
    matchesBlock (compressBlock (compressionLevels h selected) b)
        (retainedDepth (compressionLevels h selected) d) s par =
      matchesBlock b d s par := by
  cases b with
  | dummy => rfl
  | anchor _ _ => rfl
  | «variable» depth node sign =>
      have hdep := defining_mem_compressionLevels h selected (blockLevels_mem_variable hb)
      have he := projectCount_eq_iff_of_mem (compressionLevels h selected) hdep hd
      have hp : node < 2 ^ depth := by
        have hh := hv _ hb
        simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq] at hh
        exact hh.1.2
      have hpar := compressedNode_parity (compressionLevels h selected) depth node hdep hp
      cases par <;> simp [matchesBlock, compressBlock, retainedDepth, he, hpar]

theorem role_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) {b : Block} (hb : b ∈ selected)
    (m : Mode) (hm : m.depth ∈ blockLevels selected) (axis : Axis) :
    role (compressBlock (compressionLevels h selected) b)
        (compressMode (compressionLevels h selected) m) axis = role b m axis := by
  let levels := compressionLevels h selected
  have hd := defining_mem_compressionLevels h selected hm
  have hp := predecessor_mem_compressionLevels h selected hm
  have hpred := retainedDepth_pred levels m.depth hd
  have hmatch : ∀ s par, matchesBlock (compressBlock levels b) (retainedDepth levels m.depth) s par =
      matchesBlock b m.depth s par := matchesBlock_compress h selected hv hb _ hd
  have hparent : ∀ s par, matchesBlock (compressBlock levels b) (retainedDepth levels m.depth - 1) s par =
      matchesBlock b (m.depth - 1) s par := by
    rw [← hpred]
    exact matchesBlock_compress h selected hv hb _ hp
  dsimp only [levels] at *
  cases m.family <;> cases axis <;>
    simp [role, compressMode, hmatch, hparent, compressBlock_dummy_iff]

theorem variableValue_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true)
    {i p j q : Nat} {rs cs : Sign}
    (hr : Block.variable i p rs ∈ selected) (hc : Block.variable j q cs ∈ selected) :
    variableValue (retainedDepth (compressionLevels h selected) h)
        (retainedDepth (compressionLevels h selected) i)
        (compressedNode (compressionLevels h selected) i p) rs
        (retainedDepth (compressionLevels h selected) j)
        (compressedNode (compressionLevels h selected) j q) cs =
      variableValue h i p rs j q cs := by
  let levels := compressionLevels h selected
  have hi := defining_mem_compressionLevels h selected (blockLevels_mem_variable hr)
  have hj := defining_mem_compressionLevels h selected (blockLevels_mem_variable hc)
  have hh := endpoint_mem_compressionLevels h selected
  have heq := projectCount_eq_iff_of_mem levels hi hj
  have hterm := projectCount_eq_iff_of_mem levels hi hh
  have hlt := projectCount_lt_iff_of_mem levels hi hh
  have hadj := retainedDepth_adjacent_iff levels hi hj
    (fun _ => predecessor_mem_compressionLevels h selected (blockLevels_mem_variable hr))
  change (retainedDepth levels i = retainedDepth levels j ↔ i = j) at heq
  change (retainedDepth levels i = retainedDepth levels h ↔ i = h) at hterm
  change (retainedDepth levels i < retainedDepth levels h ↔ i < h) at hlt
  dsimp only [levels] at *
  simp only [variableValue, heq, hterm, hlt, hadj]
  by_cases he : i = j
  · have hcomp := compressedNode_compare h selected hv hr hc he
    simp only [if_pos he, hcomp.1, hcomp.2]
  · by_cases ha : i = j + 1
    · have hcomp := compressedNode_parent_compare h selected hv hr hc ha
      simp only [if_neg he, if_pos ha, hcomp.1, hcomp.2]
    · simp only [if_neg he, if_neg ha]

theorem hostValue_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) {r c : Block}
    (hr : r ∈ selected) (hc : c ∈ selected) :
    hostValue (retainedDepth (compressionLevels h selected) h)
        (compressBlock (compressionLevels h selected) r)
        (compressBlock (compressionLevels h selected) c) = hostValue h r c := by
  cases r with
  | anchor rm rg =>
      cases c with
      | anchor cm cg =>
          have he := compressMode_eq_iff (compressionLevels h selected) rm cm
            (defining_mem_compressionLevels h selected (blockLevels_mem_anchor hr))
            (defining_mem_compressionLevels h selected (blockLevels_mem_anchor hc))
          simp [compressBlock, hostValue, he]
      | «variable» cd cp cs =>
          have he := role_compress h selected hv hc rm (blockLevels_mem_anchor hr) .column
          simpa only [compressBlock, hostValue] using congrArg (fun n => decide (n = rg)) he
      | dummy =>
          have he := role_compress h selected hv hc rm (blockLevels_mem_anchor hr) .column
          simpa only [compressBlock, hostValue] using congrArg (fun n => decide (n = rg)) he
  | «variable» rd rp rs =>
      cases c with
      | anchor cm cg =>
          have he := role_compress h selected hv hr cm (blockLevels_mem_anchor hc) .row
          simpa only [compressBlock, hostValue] using congrArg (fun n => decide (n = cg)) he
      | «variable» cd cp cs =>
          exact variableValue_compress h selected hv hr hc
      | dummy => rfl
  | dummy =>
      cases c with
      | anchor cm cg =>
          have he := role_compress h selected hv hr cm (blockLevels_mem_anchor hc) .row
          simpa only [compressBlock, hostValue] using congrArg (fun n => decide (n = cg)) he
      | «variable» _ _ _ => rfl
      | dummy => rfl

theorem isTerminalLeaf_compress (h : Nat) (selected : List Block)
    {b : Block} (hb : b ∈ selected) :
    isTerminalLeaf (retainedDepth (compressionLevels h selected) h)
        (compressBlock (compressionLevels h selected) b) = isTerminalLeaf h b := by
  cases b with
  | anchor _ _ => rfl
  | dummy => rfl
  | «variable» d p s =>
      have he := projectCount_eq_iff_of_mem (compressionLevels h selected)
        (defining_mem_compressionLevels h selected (blockLevels_mem_variable hb))
        (endpoint_mem_compressionLevels h selected)
      cases s <;> simp [compressBlock, isTerminalLeaf, retainedDepth, he]

theorem repairedValue_compress (h : Nat) (selected : List Block)
    (hv : ∀ b ∈ selected, validBlock h b = true) {r c : Block}
    (hr : r ∈ selected) (hc : c ∈ selected) :
    repairedValue (retainedDepth (compressionLevels h selected) h)
        (compressBlock (compressionLevels h selected) r)
        (compressBlock (compressionLevels h selected) c) = repairedValue h r c := by
  simp only [repairedValue, compressBlock_dummy_iff, isTerminalLeaf_compress h selected hc,
    hostValue_compress h selected hv hr hc]

end H4Formal
