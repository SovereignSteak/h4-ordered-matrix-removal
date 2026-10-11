import H4Formal.ValidHost
import H4Formal.PhysicalHost

namespace H4Formal.Arithmetic

structure Pos where
  kind : Int
  mode : Int
  level : Int
  group : Int
  depth : Int
  node : Int
  sign : Int

def pIf (p q r : Prop) : Prop := (p ∧ q) ∨ (¬ p ∧ r)

theorem pIf_iff (p q r : Prop) [Decidable p] : pIf p q r ↔ if p then q else r := by
  by_cases hp : p <;> simp [pIf, hp]

def valid (h : Int) (p : Pos) : Prop :=
  (p.kind = 0 ∧ 0 ≤ p.mode ∧ p.mode < 6 ∧
    1 ≤ p.level ∧ p.level ≤ h ∧ (p.group = 1 ∨ p.group = 2) ∧
    p.depth = 0 ∧ p.node = 0 ∧ p.sign = 0) ∨
  (p.kind = 1 ∧ p.mode = 0 ∧ p.level = 0 ∧ p.group = 0 ∧ 0 ≤ p.depth ∧
    p.depth ≤ h ∧ 0 ≤ p.node ∧ (p.depth = 0 → p.node = 0) ∧
    pIf (p.depth = h) (p.sign = 2) (p.sign = 0 ∨ p.sign = 1)) ∨
  (p.kind = 2 ∧ p.mode = 0 ∧ p.level = 0 ∧ p.group = 0 ∧
    p.depth = 0 ∧ p.node = 0 ∧ p.sign = 0)

def modeBefore (x y : Pos) : Prop :=
  pIf (¬ (x.mode ≥ 4 ↔ y.mode ≥ 4)) (x.mode ≥ 4)
    (pIf (x.level ≠ y.level) (x.level < y.level)
      (pIf (x.mode ≠ y.mode) (x.mode < y.mode) (x.group < y.group)))

def varBefore (row : Bool) (x y : Pos) : Prop :=
  let opening : Int := if row then 1 else 0
  let closing : Int := if row then 0 else 1
  pIf (x.depth = y.depth)
    (pIf (x.node = y.node) (x.sign = opening ∧ y.sign = closing) (x.node < y.node))
    (pIf (x.depth + 1 = y.depth)
      (pIf (x.node = y.node / 2) (x.sign = opening) (x.node < y.node / 2))
      (pIf (y.depth + 1 = x.depth)
        (pIf (y.node = x.node / 2) (y.sign = closing) (x.node / 2 < y.node)) True))

def before (row : Bool) (x y : Pos) : Prop :=
  pIf (x.kind = 0) (pIf (y.kind = 0) (modeBefore x y) True)
    (pIf (y.kind = 0) False
      (pIf (x.kind = 2) (row = false ∧ y.kind = 1)
        (pIf (y.kind = 2) (row = true) (varBefore row x y))))

def atSign (p : Pos) (d s : Int) : Prop :=
  p.kind = 1 ∧ p.depth = d ∧ (p.sign = s ∨ p.sign = 2)

def atParity (p : Pos) (d s b : Int) : Prop := atSign p d s ∧ p.node % 2 = b

def signature (row : Bool) (a p : Pos) : Prop :=
  (a.mode = 0 ∧ pIf (a.group = 1)
    (if row then atSign p a.level 0 else p.kind = 2) (atSign p (a.level - 1) 0)) ∨
  (a.mode = 1 ∧ pIf (a.group = 1)
    (if row then atSign p (a.level - 1) 1 else p.kind = 2)
    (if row then atSign p a.level 1 else atSign p (a.level - 1) 1)) ∨
  (a.mode = 2 ∧ pIf (a.group = 1)
    (if row then atParity p a.level 0 0 else atSign p (a.level - 1) 0)
    (if row then p.kind = 2 else atParity p a.level 0 0)) ∨
  (a.mode = 3 ∧ pIf (a.group = 1)
    (if row then atParity p a.level 0 1 else atSign p (a.level - 1) 0)
    (if row then p.kind = 2 else atParity p a.level 0 1)) ∨
  (a.mode = 4 ∧ pIf (a.group = 1)
    (atParity p a.level 1 0)
    (if row then p.kind = 2 else atSign p (a.level - 1) 1)) ∨
  (a.mode = 5 ∧ pIf (a.group = 1)
    (atParity p a.level 1 1)
    (if row then p.kind = 2 else atSign p (a.level - 1) 1))

def variableEntry (h : Int) (r c : Pos) : Prop :=
  (r.depth = c.depth ∧
    ((r.sign = 0 ∧ c.sign = 0 ∧ r.node ≤ c.node) ∨
      (r.sign = 1 ∧ c.sign = 1 ∧ r.depth < h ∧ r.node < c.node) ∨
      (r.sign = 2 ∧ c.sign = 2 ∧ r.depth = h ∧ r.node ≤ c.node))) ∨
  (r.depth = c.depth + 1 ∧
    (((r.sign = 0 ∨ r.sign = 2) ∧ c.sign = 0 ∧ r.node / 2 ≤ c.node) ∨
      ((r.sign = 1 ∨ r.sign = 2) ∧ c.sign = 1 ∧ r.node / 2 < c.node)))

def entry (repair : Bool) (h : Int) (r c : Pos) : Prop :=
  pIf (r.kind = 0)
    (pIf (c.kind = 0) (r.mode = c.mode ∧ r.level = c.level ∧ r.group ≠ c.group)
      (signature false r c))
    (pIf (c.kind = 0) (signature true c r)
      (pIf (r.kind = 2 ∨ c.kind = 2)
        (if repair then ¬ (r.kind = 2 ∧ c.kind = 1 ∧ c.depth = h) else True)
        (variableEntry h r c)))

def terminal (h : Int) (r0 r1 r2 r3 c0 c1 c2 c3 : Pos) : Prop :=
  r0.kind = 0 ∧ r1.kind = 0 ∧ c0.kind = 0 ∧ (r0.mode = 4 ∨ r0.mode = 5) ∧
  r0.mode = r1.mode ∧ r0.mode = c0.mode ∧
  r0.level = h ∧ r1.level = h ∧ c0.level = h ∧
  r0.group = 1 ∧ r1.group = 2 ∧ c0.group = 1 ∧
  r2.kind = 1 ∧ r2.depth = h ∧ r3.kind = 2 ∧ c2.kind = 1 ∧ c2.depth = h ∧
  r2.node = c2.node ∧ c3.kind = 1 ∧ c3.depth = h - 1 ∧ c3.sign = 1 ∧
  c3.node = r2.node / 2 ∧
  ((c1.kind = 0 ∧ c1.mode = r0.mode ∧ c1.level = h ∧ c1.group = 2) ∨
   (c1.kind = 1 ∧ c1.depth = h ∧ c1.node < r2.node ∧ c1.node % 2 = r2.node % 2))

def encodeSign : Sign → Int
  | .plus => 0
  | .minus => 1
  | .leaf => 2

def encode : Block → Pos
  | .anchor m g => ⟨0, modeNumber m, m.depth, g, 0, 0, 0⟩
  | .variable d p s => ⟨1, 0, 0, 0, d, p, encodeSign s⟩
  | .dummy => ⟨2, 0, 0, 0, 0, 0, 0⟩

theorem validMode_cases (h : Nat) (m : Mode) (hm : ValidMode h m) :
    m = ⟨.v, m.depth, 0, .plus⟩ ∨ m = ⟨.v, m.depth, 0, .minus⟩ ∨
    m = ⟨.w, m.depth, 0, .plus⟩ ∨ m = ⟨.w, m.depth, 1, .plus⟩ ∨
    m = ⟨.w, m.depth, 0, .minus⟩ ∨ m = ⟨.w, m.depth, 1, .minus⟩ := by
  rcases m with ⟨f, d, p, s⟩
  rcases hm with ⟨_, _, hs, hp⟩
  cases f <;> rcases hs with rfl | rfl <;> simp [Mode.mk.injEq] at hp ⊢ <;> omega

theorem mode_eq_iff_encoded (h : Nat) (m n : Mode) (hm : ValidMode h m) (hn : ValidMode h n) :
    m = n ↔ modeNumber m = modeNumber n ∧ m.depth = n.depth := by
  obtain hm' := validMode_cases h m hm
  obtain hn' := validMode_cases h n hn
  rcases m with ⟨mf, md, mp, ms⟩
  rcases n with ⟨nf, nd, np, ns⟩
  rcases hm' with he | he | he | he | he | he <;>
    rcases hn' with hf | hf | hf | hf | hf | hf <;>
    simp only [Mode.mk.injEq] at he hf <;>
    rcases he with ⟨rfl, _, rfl, rfl⟩ <;>
    rcases hf with ⟨rfl, _, rfl, rfl⟩ <;>
    simp [modeNumber]

theorem encode_valid (h : Nat) (b : Block) (hb : ValidBlock h b) : valid h (encode b) := by
  cases b with
  | dummy => simp [valid, encode]
  | anchor m g =>
      rcases hb with ⟨⟨hd, hdh, hs, hp⟩, hg⟩
      rcases m with ⟨f, d, p, s⟩
      simp only at hd hdh hg hp
      cases f <;> rcases hs with rfl | rfl <;>
        simp [valid, encode, modeNumber, pIf] at hp ⊢ <;> omega
  | «variable» d p s =>
      rcases hb with ⟨hd, hp, hs⟩
      have hr : d = 0 → p = 0 := by intro he; subst d; simp at hp; omega
      by_cases he : d = h
      · subst d
        have hs : s = .leaf := by simpa using hs
        subst s
        simp [valid, encode, encodeSign, pIf]
        exact hr
      · have hs : s = .plus ∨ s = .minus := by simpa [he] using hs
        rcases hs with rfl | rfl <;> simp [valid, encode, encodeSign, pIf, he]
        all_goals exact ⟨by omega, hr, by omega⟩

theorem encode_signature (h : Nat) (m : Mode) (g : Nat) (hm : ValidMode h m)
    (hg : g = 1 ∨ g = 2) (b : Block) (axis : Axis) (hother : ∀ n k, b ≠ .anchor n k) :
    signature (decide (axis = .row)) (encode (.anchor m g)) (encode b) ↔ role b m axis = g := by
  have hd : 1 ≤ m.depth := hm.1
  have hc := validMode_cases h m hm
  rcases m with ⟨f, i, p, s⟩
  simp only at hd
  cases b with
  | anchor n k => exact False.elim (hother n k rfl)
  | dummy =>
      rcases hc with he | he | he | he | he | he <;>
        simp only [Mode.mk.injEq] at he <;> rcases he with ⟨rfl, _, rfl, rfl⟩ <;>
        rcases hg with rfl | rfl <;> cases axis <;>
        simp [signature, atSign, atParity, encode, modeNumber, pIf, role, matchesBlock]
  | «variable» d q sg =>
      have hp : (i - 1 : Nat) < i := by omega
      have heq : (↑(i - 1) : Int) = (i : Int) - 1 := Int.ofNat_sub hd
      rcases hc with he | he | he | he | he | he <;>
        simp only [Mode.mk.injEq] at he <;> rcases he with ⟨rfl, _, rfl, rfl⟩ <;>
        rcases hg with rfl | rfl <;> cases axis <;> cases sg <;>
        simp [signature, atSign, atParity, encode, modeNumber, pIf, role, matchesBlock,
          encodeSign, ← heq, ← Int.natCast_emod]
      all_goals first | omega | (split <;> simp_all <;> first | omega | (split <;> simp_all <;> omega))

theorem encode_variable_entry (h i p j q : Nat) (rs cs : Sign) :
    hostValue h (.variable i p rs) (.variable j q cs) = true ↔
      variableEntry h (encode (.variable i p rs)) (encode (.variable j q cs)) := by
  cases rs <;> cases cs <;> by_cases he : i = j <;> by_cases hn : i = j + 1 <;>
    simp [hostValue, variableEntry, encode, encodeSign, he, hn, ← Int.natCast_ediv,
      ← Int.natCast_add] <;> omega

theorem encode_original_entry (h : Nat) (r c : Block) (hr : ValidBlock h r) (hc : ValidBlock h c) :
    hostValue h r c = true ↔ entry false h (encode r) (encode c) := by
  cases r with
  | anchor m g =>
      rcases hr with ⟨hm, hg⟩
      cases c with
      | anchor n k =>
          rcases hc with ⟨hn, _⟩
          have he := mode_eq_iff_encoded h m n hm hn
          simp [hostValue, entry, encode, pIf, he]
          omega
      | dummy =>
          simpa [hostValue, entry, encode, pIf] using
            (encode_signature h m g hm hg .dummy .column (by intros; simp)).symm
      | «variable» d p s =>
          simpa [hostValue, entry, encode, pIf] using
            (encode_signature h m g hm hg (.variable d p s) .column (by intros; simp)).symm
  | dummy =>
      cases c with
      | anchor m g =>
          rcases hc with ⟨hm, hg⟩
          simpa [hostValue, entry, encode, pIf] using
            (encode_signature h m g hm hg .dummy .row (by intros; simp)).symm
      | dummy => simp [hostValue, entry, encode, pIf]
      | «variable» d p s => simp [hostValue, entry, encode, pIf]
  | «variable» d p s =>
      cases c with
      | anchor m g =>
          rcases hc with ⟨hm, hg⟩
          simpa [hostValue, entry, encode, pIf] using
            (encode_signature h m g hm hg (.variable d p s) .row (by intros; simp)).symm
      | dummy => simp [hostValue, entry, encode, pIf]
      | «variable» e q t =>
          simpa [entry, encode, pIf] using encode_variable_entry h d p e q s t

theorem encode_repaired_entry (h : Nat) (r c : Block) (hr : ValidBlock h r) (hc : ValidBlock h c) :
    repairedValue h r c = true ↔ entry true h (encode r) (encode c) := by
  have hor := encode_original_entry h r c hr hc
  cases r with
  | anchor m g => simpa [repairedValue, entry, encode, pIf] using hor
  | «variable» d p s =>
      cases c <;> simpa [repairedValue, entry, encode, pIf] using hor
  | dummy =>
      cases c with
      | anchor m g => simpa [repairedValue, entry, encode, pIf, isTerminalLeaf] using hor
      | dummy => simp [repairedValue, entry, encode, pIf, isTerminalLeaf, hostValue]
      | «variable» d p s =>
          rcases hc with ⟨hd, _, hs⟩
          by_cases he : d = h
          · subst d
            have hs : s = .leaf := by simpa using hs
            subst s
            simp [repairedValue, entry, encode, pIf, isTerminalLeaf]
          · rcases (show s = .plus ∨ s = .minus by simpa [he] using hs) with rfl | rfl <;>
              simp [repairedValue, entry, encode, pIf, isTerminalLeaf, hostValue] <;> omega

theorem encode_anchorBefore (h : Nat) (m n : Mode) (g k : Nat)
    (hm : ValidMode h m) (hn : ValidMode h n) (ho : anchorBefore m n g k = true) :
    modeBefore (encode (.anchor m g)) (encode (.anchor n k)) := by
  have hm' := validMode_cases h m hm
  have hn' := validMode_cases h n hn
  rcases m with ⟨mf, md, mp, ms⟩
  rcases n with ⟨nf, nd, np, ns⟩
  rcases hm' with he | he | he | he | he | he <;>
    rcases hn' with hf | hf | hf | hf | hf | hf <;>
    simp only [Mode.mk.injEq] at he hf <;>
    rcases he with ⟨rfl, _, rfl, rfl⟩ <;>
    rcases hf with ⟨rfl, _, rfl, rfl⟩ <;>
    simp [anchorBefore, earlyMode, modeBefore, encode, modeNumber, pIf] at ho ⊢
  all_goals first | omega | (split at ho <;> simp_all <;> omega)

theorem encode_variableBefore (axis : Axis) (i p j q : Nat) (s t : Sign)
    (ho : variableBefore axis i p s j q t = true) :
    varBefore (decide (axis = .row)) (encode (.variable i p s)) (encode (.variable j q t)) := by
  by_cases he : i = j
  · subst j
    cases axis <;> cases s <;> cases t <;>
      simp [variableBefore, varBefore, encode, encodeSign, pIf] at ho ⊢ <;> omega
  · by_cases hi : i + 1 = j
    · have hlt : i < j := by omega
      have hdiff : j - i = 1 := by omega
      cases axis <;> cases s <;> cases t <;>
        simp [variableBefore, nodePrefix, varBefore, encode, encodeSign, pIf,
          he, hlt, hdiff] at ho ⊢ <;> omega
    · by_cases hj : j + 1 = i
      · have hlt : ¬ i < j := by omega
        have hdiff : i - j = 1 := by omega
        cases axis <;> cases s <;> cases t <;>
          simp [variableBefore, nodePrefix, varBefore, encode, encodeSign, pIf,
            he, hlt, hdiff] at ho ⊢ <;> omega
      · cases axis <;> simp [varBefore, encode, pIf] <;> omega

theorem encode_before (h : Nat) (axis : Axis) (r c : Block)
    (hr : ValidBlock h r) (hc : ValidBlock h c) (ho : blockBefore axis r c = true) :
    before (decide (axis = .row)) (encode r) (encode c) := by
  cases r with
  | anchor m g =>
      cases c with
      | anchor n k =>
          have ha := encode_anchorBefore h m n g k hr.1 hc.1 ho
          simpa [before, encode, pIf] using ha
      | dummy => simp [before, encode, pIf]
      | «variable» d p s => simp [before, encode, pIf]
  | dummy =>
      cases c with
      | anchor m g => simp [blockBefore] at ho
      | dummy => simp [blockBefore] at ho
      | «variable» d p s => cases axis <;> simp [blockBefore] at ho <;> simp [before, encode, pIf]
  | «variable» d p s =>
      cases c with
      | anchor m g => simp [blockBefore] at ho
      | dummy => cases axis <;> simp [blockBefore] at ho <;> simp [before, encode, pIf]
      | «variable» e q t =>
          have ha := encode_variableBefore axis d p e q s t ho
          simpa [before, encode, pIf] using ha

def copy (repair : Bool) (h : Int) (r c : Fin 4 → Pos) : Prop :=
  (∀ i, valid h (r i)) ∧ (∀ i, valid h (c i)) ∧
  (∀ i j : Fin 4, i.val < j.val → before true (r i) (r j)) ∧
  (∀ i j : Fin 4, i.val < j.val → before false (c i) (c j)) ∧
  (∀ i j, entry repair h (r i) (c j) ↔ pattern i j = true)

theorem encode_copy (h : Nat) (repair : Bool) (r c : Fin 4 → Block)
    (hc : ValidCopy h (quotientHost h repair) r c) :
    copy repair h (fun i => encode (r i)) (fun i => encode (c i)) := by
  refine ⟨fun i => encode_valid h (r i) (hc.1 i),
    fun i => encode_valid h (c i) (hc.2.1 i), ?_, ?_, ?_⟩
  · intro i j hij
    apply encode_before h .row _ _ (hc.1 i) (hc.1 j)
    have ho := hc.2.2.1 i j hij
    cases repair <;> exact ho
  · intro i j hij
    apply encode_before h .column _ _ (hc.2.1 i) (hc.2.1 j)
    have ho := hc.2.2.2.1 i j hij
    cases repair <;> exact ho
  · intro i j
    have he := hc.2.2.2.2 i j
    cases repair
    · exact (encode_original_entry h _ _ (hc.1 i) (hc.2.1 j)).symm.trans (by
        simpa [quotientHost, originalHost] using congrArg (fun b => b = true) he)
    · exact (encode_repaired_entry h _ _ (hc.1 i) (hc.2.1 j)).symm.trans (by
        simpa [quotientHost, canonicalHost] using congrArg (fun b => b = true) he)

end H4Formal.Arithmetic
