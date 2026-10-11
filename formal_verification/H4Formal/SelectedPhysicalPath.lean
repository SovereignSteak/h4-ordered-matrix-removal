import H4Formal.ProtectedAvoidance
import H4Formal.ConcreteFrames

namespace H4Formal

def levelSign (h d : Nat) (s : Sign) : Sign := if d = h then .leaf else s

def selectedVariable (h d a b own : Nat) (hd : d ≤ h) (ha : a < 2 ^ h)
    (hb : b < 2 ^ h) (s : Sign) (hs : s = .plus ∨ s = .minus) : PhysicalPosition h where
  block := .variable d (sampleNode h d a b) (levelSign h d s)
  valid := by
    refine ⟨hd, sampleNode_lt h d a b hd ha hb, ?_⟩
    by_cases he : d = h <;> simp [levelSign, he, hs]
  offset := sampleOffset h d own
  offset_lt := sampleOffset_lt h d own

def selectedAnchor (h _a _b own : Nat) (hown : own < 2 ^ h)
    (m : Mode) (hm : ValidMode h m) (g : Nat) (hg : g = 1 ∨ g = 2) : PhysicalPosition h :=
  ⟨.anchor m g, ⟨hm, hg⟩, own, hown⟩

def selectedDummy (h own : Nat) (ho : own < 2 ^ h) : PhysicalPosition h :=
  ⟨.dummy, True.intro, own, ho⟩

theorem selectedVariable_selected (h d a b own : Nat) (hd : d ≤ h)
    (ha : a < 2 ^ h) (hb : b < 2 ^ h) (s : Sign) (hs : s = .plus ∨ s = .minus) :
    SelectedPosition h a b own (selectedVariable h d a b own hd ha hb s hs) := by
  exact ⟨rfl, rfl⟩

theorem selectedAnchor_selected (h a b own : Nat) (ho : own < 2 ^ h)
    (m : Mode) (hm : ValidMode h m) (g : Nat) (hg : g = 1 ∨ g = 2) :
    SelectedPosition h a b own (selectedAnchor h a b own ho m hm g hg) := rfl

theorem selectedDummy_selected (h a b own : Nat) (ho : own < 2 ^ h) :
    SelectedPosition h a b own (selectedDummy h own ho) := rfl

theorem vMode_valid (h i : Nat) (hi : 1 ≤ i) (hih : i ≤ h) (s : Sign)
    (hs : s = .plus ∨ s = .minus) : ValidMode h (vMode i s) := by
  exact ⟨hi, hih, hs, rfl⟩

theorem wMode_valid (h i p : Nat) (hi : 1 ≤ i) (hih : i ≤ h) (s : Sign)
    (hs : s = .plus ∨ s = .minus) : ValidMode h (wMode i p s) := by
  exact ⟨hi, hih, hs, Nat.mod_lt p (by decide)⟩

theorem selectedVariable_leaf_shared (h a b own : Nat) (ha : a < 2 ^ h) (hb : b < 2 ^ h) :
    selectedVariable h h a b own (Nat.le_refl h) ha hb .plus (Or.inl rfl) =
    selectedVariable h h a b own (Nat.le_refl h) ha hb .minus (Or.inr rfl) := by
  simp [selectedVariable, levelSign]

theorem physical_frame_of_block_frame (h : Nat)
    (r0 r1 x y c0 c1 u v : PhysicalPosition h)
    (f : MarkerFrame (asMatrix (originalHost h)) r0.block r1.block x.block y.block
      c0.block c1.block u.block v.block) :
    MarkerFrame (physicalHost h) r0 r1 x y c0 c1 u v := by
  constructor
  · exact ⟨Or.inl f.rows.1, Or.inl f.rows.2.1, Or.inl f.rows.2.2.1,
      Or.inl f.rows.2.2.2.1, Or.inl f.rows.2.2.2.2.1, Or.inl f.rows.2.2.2.2.2⟩
  · exact ⟨Or.inl f.cols.1, Or.inl f.cols.2.1, Or.inl f.cols.2.2.1,
      Or.inl f.cols.2.2.2.1, Or.inl f.cols.2.2.2.2.1, Or.inl f.cols.2.2.2.2.2⟩
  · exact f.a00
  · exact f.a01
  · exact f.a10
  · exact f.a11
  · exact f.a02
  · exact f.a03
  · exact f.a12
  · exact f.a13
  · exact f.a20
  · exact f.a21
  · exact f.a30
  · exact f.a31

def editedHost (h : Nat) (D : PhysicalPosition h → PhysicalPosition h → Bool) :
    OrderedMatrix (PhysicalPosition h) (PhysicalPosition h) where
  value := D
  rowBefore := physicalBefore .row
  colBefore := physicalBefore .column

theorem protected_frame_survives (h a b : Nat)
    (D : PhysicalPosition h → PhysicalPosition h → Bool)
    (unchanged : ∀ r c, ProtectedCell h a b r c → D r c = hostValue h r.block c.block)
    (r0 r1 x y c0 c1 u v : PhysicalPosition h)
    (hr : ∀ r ∈ [r0, r1, x, y], SelectedPosition h a b a r)
    (hc : ∀ c ∈ [c0, c1, u, v], SelectedPosition h a b b c)
    (hr0 : NonVariable r0.block) (hr1 : NonVariable r1.block)
    (hc0 : NonVariable c0.block) (hc1 : NonVariable c1.block)
    (f : MarkerFrame (physicalHost h) r0 r1 x y c0 c1 u v) :
    MarkerFrame (editedHost h D) r0 r1 x y c0 c1 u v := by
  have keep : ∀ r ∈ [r0, r1, x, y], ∀ c ∈ [c0, c1, u, v],
      (NonVariable r.block ∨ NonVariable c.block) →
      D r c = hostValue h r.block c.block := by
    intro r hrr c hcc hn
    apply unchanged r c
    exact ⟨hr r hrr, hc c hcc, hn.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  constructor
  · exact f.rows
  · exact f.cols
  · exact (keep r0 (by simp) c0 (by simp) (Or.inl hr0)).trans f.a00
  · exact (keep r0 (by simp) c1 (by simp) (Or.inl hr0)).trans f.a01
  · exact (keep r1 (by simp) c0 (by simp) (Or.inl hr1)).trans f.a10
  · exact (keep r1 (by simp) c1 (by simp) (Or.inl hr1)).trans f.a11
  · exact (keep r0 (by simp) u (by simp) (Or.inl hr0)).trans f.a02
  · exact (keep r0 (by simp) v (by simp) (Or.inl hr0)).trans f.a03
  · exact (keep r1 (by simp) u (by simp) (Or.inl hr1)).trans f.a12
  · exact (keep r1 (by simp) v (by simp) (Or.inl hr1)).trans f.a13
  · exact (keep x (by simp) c0 (by simp) (Or.inr hc0)).trans f.a20
  · exact (keep x (by simp) c1 (by simp) (Or.inr hc1)).trans f.a21
  · exact (keep y (by simp) c0 (by simp) (Or.inr hc0)).trans f.a30
  · exact (keep y (by simp) c1 (by simp) (Or.inr hc1)).trans f.a31

end H4Formal
