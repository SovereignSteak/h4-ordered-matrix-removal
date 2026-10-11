import H4Formal.Transfer

namespace H4Formal

/-- Exactly the six modes per positive level; V parity is canonical zero. -/
def ValidMode (h : Nat) (m : Mode) : Prop :=
  1 ≤ m.depth ∧ m.depth ≤ h ∧
  (m.sign = .plus ∨ m.sign = .minus) ∧
  (match m.family with
   | .v => m.parity = 0
   | .w => m.parity < 2)

def ValidBlock (h : Nat) : Block → Prop
  | .anchor m g => ValidMode h m ∧ (g = 1 ∨ g = 2)
  | .variable d p s => d ≤ h ∧ p < 2 ^ d ∧
      (if d = h then s = .leaf else s = .plus ∨ s = .minus)
  | .dummy => True

instance (h : Nat) (m : Mode) : Decidable (ValidMode h m) := by
  unfold ValidMode
  cases m.family <;> infer_instance

instance (h : Nat) (b : Block) : Decidable (ValidBlock h b) := by
  cases b <;> unfold ValidBlock <;> infer_instance

def modeNumber (m : Mode) : Nat :=
  match m.family, m.sign with
  | .v, .plus => 0
  | .v, _ => 1
  | .w, .plus => 2 + m.parity
  | .w, _ => 4 + m.parity

def earlyMode (m : Mode) : Bool :=
  decide (m.family = .w ∧ m.sign = .minus)

/-- W-minus prefix, then depth, mode number, and internal group. -/
def anchorBefore (m n : Mode) (g k : Nat) : Bool :=
  if earlyMode m ≠ earlyMode n then earlyMode m
  else if m.depth ≠ n.depth then decide (m.depth < n.depth)
  else if modeNumber m ≠ modeNumber n then decide (modeNumber m < modeNumber n)
  else decide (g < k)

/-- Node prefix of length `d` of a longer, depth-`e` node. -/
def nodePrefix (p e d : Nat) : Nat := p / 2 ^ (e - d)

/-- Literal DFS order: minus opens a row subtree, plus opens a column subtree. -/
def variableBefore (axis : Axis) (i p : Nat) (s : Sign)
    (j q : Nat) (t : Sign) : Bool :=
  if i = j then
    if p = q then
      match axis with
      | .row => decide (s = .minus ∧ t = .plus)
      | .column => decide (s = .plus ∧ t = .minus)
    else decide (p < q)
  else if i < j then
    if p = nodePrefix q j i then
      match axis with
      | .row => decide (s = .minus)
      | .column => decide (s = .plus)
    else decide (p < nodePrefix q j i)
  else
    if q = nodePrefix p i j then
      match axis with
      | .row => decide (t = .plus)
      | .column => decide (t = .minus)
    else decide (nodePrefix p i j < q)

def blockBefore (axis : Axis) : Block → Block → Bool
  | .anchor m g, .anchor n k => anchorBefore m n g k
  | .anchor _ _, _ => true
  | _, .anchor _ _ => false
  | .dummy, .dummy => false
  | .dummy, .variable _ _ _ => decide (axis = .column)
  | .variable _ _ _, .dummy => decide (axis = .row)
  | .variable i p s, .variable j q t => variableBefore axis i p s j q t

def originalHost (h : Nat) : OrderedBlockHost where
  value := hostValue h
  rowBefore r s := blockBefore .row r s = true
  colBefore r s := blockBefore .column r s = true

def canonicalHost (h : Nat) : OrderedBlockHost where
  value := repairedValue h
  rowBefore r s := blockBefore .row r s = true
  colBefore r s := blockBefore .column r s = true

def ValidCopy (h : Nat) (H : OrderedBlockHost) (r c : Fin 4 → Block) : Prop :=
  (∀ i, ValidBlock h (r i)) ∧ (∀ j, ValidBlock h (c j)) ∧ IsCopy H r c

theorem blockBefore_irrefl (axis : Axis) (b : Block) :
    blockBefore axis b b = false := by
  cases b with
  | anchor m g => simp [blockBefore, anchorBefore]
  | dummy => rfl
  | «variable» d p s =>
      cases axis <;> cases s <;> simp [blockBefore, variableBefore]

theorem copy_row_types_distinct (H : OrderedBlockHost)
    (hOrder : ∀ b, ¬ H.rowBefore b b) (r c : Fin 4 → Block)
    (hc : IsCopy H r c) : ∀ i j, i ≠ j → r i ≠ r j := by
  intro i j hne heq
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hij | hji
  · exact hOrder _ (heq ▸ hc.1 i j hij)
  · exact hOrder _ (heq ▸ hc.1 j i hji)

theorem copy_column_types_distinct (H : OrderedBlockHost)
    (hOrder : ∀ b, ¬ H.colBefore b b) (r c : Fin 4 → Block)
    (hc : IsCopy H r c) : ∀ i j, i ≠ j → c i ≠ c j := by
  intro i j hne heq
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hij | hji
  · exact hOrder _ (heq ▸ hc.2.1 i j hij)
  · exact hOrder _ (heq ▸ hc.2.1 j i hji)

end H4Formal
