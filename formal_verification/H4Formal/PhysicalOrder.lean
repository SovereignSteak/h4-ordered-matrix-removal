import H4Formal.HostSize
import H4Formal.ArithmeticHost

namespace H4Formal

def orderStride (h : Nat) := 2 * h + 3
def nodeLeft (h d p : Nat) := p * 2 ^ (h - d)
def nodeRight (h d p : Nat) := (p + 1) * 2 ^ (h - d)
def nodeFirst (h d p : Nat) := nodeLeft h d p * orderStride h + h + 1 + d
def nodeLast (h d p : Nat) := nodeRight h d p * orderStride h + (h - d)

def variableRank (axis : Axis) (h d p : Nat) (s : Sign) : Nat :=
  match axis, s with
  | .row, .minus | .column, .plus => nodeFirst h d p
  | .row, .plus | .column, .minus => nodeLast h d p
  | _, .leaf => p * orderStride h + 2 * h + 2

theorem nodeFirst_lt_nodeLast (h d p : Nat) (hd : d ≤ h) :
    nodeFirst h d p < nodeLast h d p := by
  have hp : 1 ≤ 2 ^ (h - d) := Nat.pow_pos (by decide)
  have hm := Nat.mul_le_mul_right (orderStride h) hp
  simp only [Nat.one_mul] at hm
  simp only [nodeFirst, nodeLast, nodeLeft, nodeRight, Nat.add_mul, Nat.one_mul]
  unfold orderStride at hm ⊢
  omega

theorem variableRank_bounds (axis : Axis) (h d p : Nat) (s : Sign)
    (hb : ValidBlock h (.variable d p s)) :
    nodeFirst h d p ≤ variableRank axis h d p s ∧
      variableRank axis h d p s ≤ nodeLast h d p := by
  have ho := Nat.le_of_lt (nodeFirst_lt_nodeLast h d p hb.1)
  by_cases he : d = h
  · subst d
    have hs : s = .leaf := by simpa [ValidBlock] using hb.2.2
    subst s
    cases axis <;> simp [variableRank, nodeFirst, nodeLast, nodeLeft, nodeRight,
      orderStride, Nat.add_mul, Nat.mul_add] <;> omega
  · have hs : s = .plus ∨ s = .minus := by simpa [ValidBlock, he] using hb.2.2
    rcases hs with rfl | rfl <;> cases axis <;> simp [variableRank, ho]

theorem node_intervals_nested (h i j q : Nat) (hij : i ≤ j) (hj : j ≤ h) :
    nodeLeft h i (nodePrefix q j i) ≤ nodeLeft h j q ∧
      nodeRight h j q ≤ nodeRight h i (nodePrefix q j i) := by
  have hf : 0 < 2 ^ (j - i) := Nat.pow_pos (by decide)
  have he : 2 ^ (h - i) = 2 ^ (j - i) * 2 ^ (h - j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hlo := Nat.div_mul_le_self q (2 ^ (j - i))
  have hhi : q + 1 ≤ (q / 2 ^ (j - i) + 1) * 2 ^ (j - i) := by
    have hh := Nat.mod_lt q hf
    have hd := Nat.mod_add_div q (2 ^ (j - i))
    have hc := Nat.mul_comm (q / 2 ^ (j - i)) (2 ^ (j - i))
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hlo' := Nat.mul_le_mul_right (2 ^ (h - j)) hlo
  have hhi' := Nat.mul_le_mul_right (2 ^ (h - j)) hhi
  simpa only [nodeLeft, nodeRight, nodePrefix, he, Nat.mul_assoc] using And.intro hlo' hhi'

theorem nodeFirst_ancestor_lt (h i j q : Nat) (hij : i < j) (hj : j ≤ h) :
    nodeFirst h i (nodePrefix q j i) < nodeFirst h j q := by
  have hl := (node_intervals_nested h i j q (by omega) hj).1
  have hm := Nat.mul_le_mul_right (orderStride h) hl
  unfold nodeFirst
  omega

theorem nodeLast_descendant_lt (h i j q : Nat) (hij : i < j) (hj : j ≤ h) :
    nodeLast h j q < nodeLast h i (nodePrefix q j i) := by
  have hr := (node_intervals_nested h i j q (by omega) hj).2
  have hm := Nat.mul_le_mul_right (orderStride h) hr
  unfold nodeLast
  omega

theorem interval_rank_separation (h i p j q : Nat)
    (hi : i ≤ h) (_hj : j ≤ h) (he : nodeRight h i p ≤ nodeLeft h j q) :
    nodeLast h i p < nodeFirst h j q := by
  have hm := Nat.mul_le_mul_right (orderStride h) he
  unfold nodeLast nodeFirst
  omega

theorem variableRank_same_depth_separation (axis : Axis) (h d p q : Nat) (s t : Sign)
    (hp : ValidBlock h (.variable d p s)) (hq : ValidBlock h (.variable d q t))
    (hpq : p < q) : variableRank axis h d p s < variableRank axis h d q t := by
  have he : nodeRight h d p ≤ nodeLeft h d q :=
    Nat.mul_le_mul_right _ (by omega)
  have hs := interval_rank_separation h d p d q hp.1 hq.1 he
  have hl := variableRank_bounds axis h d p s hp
  have hr := variableRank_bounds axis h d q t hq
  omega

theorem variableRank_disjoint_separation (axis : Axis) (h i p j q : Nat) (s t : Sign)
    (hp : ValidBlock h (.variable i p s)) (hq : ValidBlock h (.variable j q t))
    (hij : i ≤ j) (hpq : p < nodePrefix q j i) :
    variableRank axis h i p s < variableRank axis h j q t := by
  have hn := (node_intervals_nested h i j q hij hq.1).1
  have he : nodeRight h i p ≤ nodeLeft h i (nodePrefix q j i) :=
    Nat.mul_le_mul_right _ (by omega)
  have hs := interval_rank_separation h i p j q hp.1 hq.1 (Nat.le_trans he hn)
  have hl := variableRank_bounds axis h i p s hp
  have hr := variableRank_bounds axis h j q t hq
  omega

theorem variableRank_reverse_disjoint_separation (axis : Axis) (h i p j q : Nat) (s t : Sign)
    (hp : ValidBlock h (.variable i p s)) (hq : ValidBlock h (.variable j q t))
    (hij : i ≤ j) (hpq : nodePrefix q j i < p) :
    variableRank axis h j q t < variableRank axis h i p s := by
  have hn := (node_intervals_nested h i j q hij hq.1).2
  have he : nodeRight h i (nodePrefix q j i) ≤ nodeLeft h i p :=
    Nat.mul_le_mul_right _ (by omega)
  have hs := interval_rank_separation h j q i p hq.1 hp.1 (Nat.le_trans hn he)
  have hl := variableRank_bounds axis h j q t hq
  have hr := variableRank_bounds axis h i p s hp
  omega

theorem variableBefore_rank (axis : Axis) (h i p j q : Nat) (s t : Sign)
    (hp : ValidBlock h (.variable i p s)) (hq : ValidBlock h (.variable j q t)) :
    variableBefore axis i p s j q t = true ↔
      variableRank axis h i p s < variableRank axis h j q t := by
  by_cases he : i = j
  · subst j
    by_cases heq : p = q
    · subst q
      have ho := nodeFirst_lt_nodeLast h i p hp.1
      by_cases hi : i = h
      · have hs : s = .leaf := by simpa [ValidBlock, hi] using hp.2.2
        have ht : t = .leaf := by simpa [ValidBlock, hi] using hq.2.2
        subst s; subst t
        cases axis <;> simp [variableBefore, variableRank]
      · have hs : s = .plus ∨ s = .minus := by simpa [ValidBlock, hi] using hp.2.2
        have ht : t = .plus ∨ t = .minus := by simpa [ValidBlock, hi] using hq.2.2
        rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> cases axis <;>
          simp [variableBefore, variableRank] <;> omega
    · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
      · have ho := variableRank_same_depth_separation axis h i p q s t hp hq hlt
        simp [variableBefore, heq, hlt, ho]
      · have ho := variableRank_same_depth_separation axis h i q p t s hq hp hgt
        simp [variableBefore, heq]
        omega
  · by_cases hij : i < j
    · by_cases heq : p = nodePrefix q j i
      · subst p
        have ho := nodeFirst_ancestor_lt h i j q hij hq.1
        have hc := nodeLast_descendant_lt h i j q hij hq.1
        have hr := variableRank_bounds axis h j q t hq
        have hi : i ≠ h := by have := hq.1; omega
        have hs : s = .plus ∨ s = .minus := by simpa [ValidBlock, hi] using hp.2.2
        rcases hs with rfl | rfl <;> cases axis <;>
          simp [variableBefore, he, hij, variableRank] at hr ⊢ <;> omega
      · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
        · have ho := variableRank_disjoint_separation axis h i p j q s t hp hq (by omega) hlt
          simp [variableBefore, he, hij, heq, hlt, ho]
        · have ho := variableRank_reverse_disjoint_separation axis h i p j q s t hp hq (by omega) hgt
          simp [variableBefore, he, hij, heq]
          omega
    · have hji : j < i := by omega
      by_cases heq : q = nodePrefix p i j
      · subst q
        have ho := nodeFirst_ancestor_lt h j i p hji hp.1
        have hc := nodeLast_descendant_lt h j i p hji hp.1
        have hr := variableRank_bounds axis h i p s hp
        have hj : j ≠ h := by have := hp.1; omega
        have ht : t = .plus ∨ t = .minus := by simpa [ValidBlock, hj] using hq.2.2
        rcases ht with rfl | rfl <;> cases axis <;>
          simp [variableBefore, he, hij, variableRank] at hr ⊢ <;> omega
      · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
        · have ho := variableRank_disjoint_separation axis h j q i p t s hq hp (by omega) hlt
          simp [variableBefore, he, hij, heq]
          omega
        · have ho := variableRank_reverse_disjoint_separation axis h j q i p t s hq hp (by omega) hgt
          simp [variableBefore, he, hij, heq, ho]
          omega

theorem modeNumber_bound (h : Nat) (m : Mode) (hm : ValidMode h m) : modeNumber m < 6 := by
  rcases m with ⟨f, d, p, s⟩
  cases f <;> cases s <;> simp [ValidMode, modeNumber] at hm ⊢ <;> omega

def anchorRank (h : Nat) (m : Mode) (g : Nat) : Nat :=
  (if earlyMode m then 0 else 12 * h + 13) + 12 * m.depth + 2 * modeNumber m + g

theorem anchorBefore_rank (h : Nat) (m n : Mode) (g k : Nat)
    (hm : ValidMode h m) (hn : ValidMode h n) (hg : g = 1 ∨ g = 2) (hk : k = 1 ∨ k = 2) :
    anchorBefore m n g k = true ↔ anchorRank h m g < anchorRank h n k := by
  have hmn := modeNumber_bound h m hm
  have hnn := modeNumber_bound h n hn
  have hmd := hm.2.1
  have hnd := hn.2.1
  by_cases hd : m.depth = n.depth <;>
    by_cases he : modeNumber m = modeNumber n <;>
    cases hx : earlyMode m <;> cases hy : earlyMode n <;>
    simp [anchorBefore, anchorRank, hx, hy, hd, he] <;> omega

theorem anchorRank_injective (h : Nat) (m n : Mode) (g k : Nat)
    (hm : ValidMode h m) (hn : ValidMode h n) (hg : g = 1 ∨ g = 2) (hk : k = 1 ∨ k = 2)
    (he : anchorRank h m g = anchorRank h n k) : m = n ∧ g = k := by
  have hmn := modeNumber_bound h m hm
  have hnn := modeNumber_bound h n hn
  have hmd := hm.2.1
  have hnd := hn.2.1
  have hh : m.depth = n.depth ∧ modeNumber m = modeNumber n ∧ g = k := by
    cases hx : earlyMode m <;> cases hy : earlyMode n <;>
      simp [anchorRank, hx, hy] at he <;> omega
  refine ⟨?_, hh.2.2⟩
  apply (Arithmetic.mode_eq_iff_encoded h m n hm hn).2
  exact ⟨hh.2.1, hh.1⟩

theorem variableBefore_total (axis : Axis) (h i p j q : Nat) (s t : Sign)
    (hp : ValidBlock h (.variable i p s)) (hq : ValidBlock h (.variable j q t)) :
    variableBefore axis i p s j q t = true ∨
      variableBefore axis j q t i p s = true ∨ (i = j ∧ p = q ∧ s = t) := by
  by_cases he : i = j
  · subst j
    by_cases heq : p = q
    · subst q
      cases axis <;> cases s <;> cases t <;>
        simp [variableBefore, ValidBlock] at hp hq ⊢ <;> omega
    · simp [variableBefore, heq, Ne.symm heq]
      omega
  · by_cases hij : i < j
    · have hji : ¬ j < i := by omega
      have hi : i ≠ h := by have := hq.1; omega
      have hs : s = .plus ∨ s = .minus := by simpa [ValidBlock, hi] using hp.2.2
      rcases hs with rfl | rfl <;> cases axis <;>
        simp [variableBefore, he, Ne.symm he, hij, hji] <;>
        by_cases heq : p = nodePrefix q j i <;> simp [heq] <;> omega
    · have hji : j < i := by omega
      have hj : j ≠ h := by have := hp.1; omega
      have ht : t = .plus ∨ t = .minus := by simpa [ValidBlock, hj] using hq.2.2
      rcases ht with rfl | rfl <;> cases axis <;>
        simp [variableBefore, he, Ne.symm he, hij, hji] <;>
        by_cases heq : q = nodePrefix p i j <;> simp [heq] <;> omega

theorem variableRank_injective (axis : Axis) (h i p j q : Nat) (s t : Sign)
    (hp : ValidBlock h (.variable i p s)) (hq : ValidBlock h (.variable j q t))
    (he : variableRank axis h i p s = variableRank axis h j q t) :
    i = j ∧ p = q ∧ s = t := by
  rcases variableBefore_total axis h i p j q s t hp hq with ho | ho | heq
  · have hlt := (variableBefore_rank axis h i p j q s t hp hq).1 ho
    omega
  · have hlt := (variableBefore_rank axis h j q i p t s hq hp).1 ho
    omega
  · exact heq

def blockOrderKey (axis : Axis) (h : Nat) : Block → Nat × Nat
  | .anchor m g => (0, anchorRank h m g)
  | .variable d p s => (if axis = .row then 1 else 2, variableRank axis h d p s)
  | .dummy => (if axis = .row then 2 else 1, 0)

def keyBefore (x y : Nat × Nat) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

theorem blockBefore_key (axis : Axis) (h : Nat) (x y : Block)
    (hx : ValidBlock h x) (hy : ValidBlock h y) :
    blockBefore axis x y = true ↔ keyBefore (blockOrderKey axis h x) (blockOrderKey axis h y) := by
  cases x with
  | anchor m g =>
      cases y with
      | anchor n k => simpa [blockBefore, blockOrderKey, keyBefore] using
          anchorBefore_rank h m n g k hx.1 hy.1 hx.2 hy.2
      | «variable» d p s => cases axis <;> simp [blockBefore, blockOrderKey, keyBefore]
      | dummy =>
          cases axis <;> simp [blockBefore, blockOrderKey, keyBefore, anchorRank]
  | «variable» d p s =>
      cases y with
      | anchor m g => cases axis <;> simp [blockBefore, blockOrderKey, keyBefore]
      | «variable» e q t => simpa [blockBefore, blockOrderKey, keyBefore] using
          variableBefore_rank axis h d p e q s t hx hy
      | dummy => cases axis <;> simp [blockBefore, blockOrderKey, keyBefore]
  | dummy => cases y <;> cases axis <;> simp [blockBefore, blockOrderKey, keyBefore, anchorRank]

theorem blockOrderKey_injective (axis : Axis) (h : Nat) (x y : Block)
    (hx : ValidBlock h x) (hy : ValidBlock h y)
    (he : blockOrderKey axis h x = blockOrderKey axis h y) : x = y := by
  cases x with
  | anchor m g =>
      cases y with
      | anchor n k =>
          have hpair := Prod.mk.inj he
          rcases anchorRank_injective h m n g k hx.1 hy.1 hx.2 hy.2 hpair.2 with ⟨rfl, rfl⟩
          rfl
      | «variable» d p s => cases axis <;> simp [blockOrderKey] at he
      | dummy => cases axis <;> simp [blockOrderKey, anchorRank] at he
  | «variable» d p s =>
      cases y with
      | anchor m g => cases axis <;> simp [blockOrderKey] at he
      | «variable» e q t =>
          have hpair := Prod.mk.inj he
          rcases variableRank_injective axis h d p e q s t hx hy hpair.2 with ⟨rfl, rfl, rfl⟩
          rfl
      | dummy => cases axis <;> simp [blockOrderKey] at he
  | dummy => cases y <;> cases axis <;> simp [blockOrderKey, anchorRank] at he ⊢

theorem physicalBefore_total (axis : Axis) (h : Nat) (x y : PhysicalPosition h) :
    physicalBefore axis x y ∨ x = y ∨ physicalBefore axis y x := by
  have hx := blockBefore_key axis h x.block y.block x.valid y.valid
  have hy := blockBefore_key axis h y.block x.block y.valid x.valid
  by_cases he : blockOrderKey axis h x.block = blockOrderKey axis h y.block
  · have hb := blockOrderKey_injective axis h x.block y.block x.valid y.valid he
    by_cases ho : x.offset = y.offset
    · exact Or.inr (Or.inl (physicalPosition_ext x y hb ho))
    · rcases Nat.lt_or_gt_of_ne ho with hlt | hgt
      · exact Or.inl (Or.inr ⟨hb, hlt⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hb.symm, hgt⟩))
  · have hk : keyBefore (blockOrderKey axis h x.block) (blockOrderKey axis h y.block) ∨
        keyBefore (blockOrderKey axis h y.block) (blockOrderKey axis h x.block) := by
      have hn : ¬ ((blockOrderKey axis h x.block).1 = (blockOrderKey axis h y.block).1 ∧
          (blockOrderKey axis h x.block).2 = (blockOrderKey axis h y.block).2) :=
        fun hh => he (Prod.ext hh.1 hh.2)
      unfold keyBefore
      omega
    rcases hk with hk | hk
    · exact Or.inl (Or.inl (hx.2 hk))
    · exact Or.inr (Or.inr (Or.inl (hy.2 hk)))

theorem physicalBefore_irrefl (axis : Axis) (h : Nat) (x : PhysicalPosition h) :
    ¬ physicalBefore axis x x := by
  simp [physicalBefore, blockBefore_irrefl]

theorem physicalBefore_trans (axis : Axis) (h : Nat) (x y z : PhysicalPosition h)
    (hxy : physicalBefore axis x y) (hyz : physicalBefore axis y z) :
    physicalBefore axis x z := by
  have hkeyxy := blockBefore_key axis h x.block y.block x.valid y.valid
  have hkeyyz := blockBefore_key axis h y.block z.block y.valid z.valid
  have hkeyxz := blockBefore_key axis h x.block z.block x.valid z.valid
  rcases hxy with hxy | ⟨hxy, hxo⟩ <;> rcases hyz with hyz | ⟨hyz, hyo⟩
  · left
    apply hkeyxz.2
    have hx := hkeyxy.1 hxy
    have hy := hkeyyz.1 hyz
    unfold keyBefore at *
    omega
  · left
    simpa only [← hyz] using hxy
  · left
    simpa only [hxy] using hyz
  · right
    exact ⟨hxy.trans hyz, Nat.lt_trans hxo hyo⟩

end H4Formal
