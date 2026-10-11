import H4Formal.XorSampling

namespace H4Formal

def NonVariable : Block → Prop
  | .variable _ _ _ => False
  | _ => True

def RootBlock : Block → Prop
  | .variable d p s => d = 0 ∧ p = 0 ∧ (s = .plus ∨ s = .minus)
  | _ => False

/-- Each row uses coordinate `a` and each column uses coordinate `b`. -/
def SelectedPosition (h a b own : Nat) (x : PhysicalPosition h) : Prop :=
  match x.block with
  | .variable d p _ => p = sampleNode h d a b ∧ x.offset = sampleOffset h d own
  | _ => x.offset = own

/-- Protected cells have a marker or dummy endpoint, or two root endpoints. -/
def ProtectedCell (h a b : Nat) (r c : PhysicalPosition h) : Prop :=
  SelectedPosition h a b a r ∧ SelectedPosition h a b b c ∧
    (NonVariable r.block ∨ NonVariable c.block ∨ (RootBlock r.block ∧ RootBlock c.block))

instance (b : Block) : Decidable (NonVariable b) := by
  cases b <;> unfold NonVariable <;> infer_instance

instance (b : Block) : Decidable (RootBlock b) := by
  cases b <;> unfold RootBlock <;> infer_instance

instance (h a b own : Nat) (x : PhysicalPosition h) :
    Decidable (SelectedPosition h a b own x) := by
  unfold SelectedPosition
  cases x.block <;> infer_instance

instance (h a b : Nat) (r c : PhysicalPosition h) : Decidable (ProtectedCell h a b r c) := by
  unfold ProtectedCell
  infer_instance

theorem selected_nonvariable_coordinate (h a b own : Nat) (x : PhysicalPosition h)
    (hn : NonVariable x.block) (hs : SelectedPosition h a b own x) : x.offset = own := by
  cases hb : x.block <;> simp [NonVariable, SelectedPosition, hb] at hn hs ⊢
  all_goals exact hs

theorem selected_variable_coordinates (h a b own d p : Nat) (s : Sign)
    (x : PhysicalPosition h) (hb : x.block = .variable d p s)
    (hs : SelectedPosition h a b own x) :
    p = sampleNode h d a b ∧ x.offset = sampleOffset h d own := by
  simpa [SelectedPosition, hb] using hs

/-- A fixed protected physical cell can occur in at most one of the `m^2` selections. -/
theorem protected_cell_sample_injective (h a b a' b' : Nat)
    (ha : a < 2 ^ h) (hb : b < 2 ^ h) (ha' : a' < 2 ^ h) (hb' : b' < 2 ^ h)
    (r c : PhysicalPosition h)
    (hs : ProtectedCell h a b r c) (hs' : ProtectedCell h a' b' r c) :
    a = a' ∧ b = b' := by
  rcases hs with ⟨hr, hc, hn⟩
  rcases hs' with ⟨hr', hc', _⟩
  rcases hn with hnr | hnc | ⟨hrr, hcc⟩
  · have hae : a = a' := (selected_nonvariable_coordinate h a b a r hnr hr).symm.trans
      (selected_nonvariable_coordinate h a' b' a' r hnr hr')
    cases hcb : c.block with
    | anchor m g =>
        have hn : NonVariable c.block := by simp [NonVariable, hcb]
        exact ⟨hae, (selected_nonvariable_coordinate h a b b c hn hc).symm.trans
          (selected_nonvariable_coordinate h a' b' b' c hn hc')⟩
    | dummy =>
        have hn : NonVariable c.block := by simp [NonVariable, hcb]
        exact ⟨hae, (selected_nonvariable_coordinate h a b b c hn hc).symm.trans
          (selected_nonvariable_coordinate h a' b' b' c hn hc')⟩
    | «variable» d p s =>
        have hu := selected_variable_coordinates h a b b d p s c hcb hc
        have hv := selected_variable_coordinates h a' b' b' d p s c hcb hc'
        exact sample_marker_column_injective h d a b a' b' hae
          (hu.1.symm.trans hv.1) (hu.2.symm.trans hv.2)
  · have hbe : b = b' := (selected_nonvariable_coordinate h a b b c hnc hc).symm.trans
      (selected_nonvariable_coordinate h a' b' b' c hnc hc')
    cases hrb : r.block with
    | anchor m g =>
        have hn : NonVariable r.block := by simp [NonVariable, hrb]
        exact ⟨(selected_nonvariable_coordinate h a b a r hn hr).symm.trans
          (selected_nonvariable_coordinate h a' b' a' r hn hr'), hbe⟩
    | dummy =>
        have hn : NonVariable r.block := by simp [NonVariable, hrb]
        exact ⟨(selected_nonvariable_coordinate h a b a r hn hr).symm.trans
          (selected_nonvariable_coordinate h a' b' a' r hn hr'), hbe⟩
    | «variable» d p s =>
        have hu := selected_variable_coordinates h a b a d p s r hrb hr
        have hv := selected_variable_coordinates h a' b' a' d p s r hrb hr'
        exact sample_row_marker_injective h d a b a' b' (hu.1.symm.trans hv.1)
          (hu.2.symm.trans hv.2) hbe
  · have rcoord : r.offset = a ∧ r.offset = a' := by
      cases hrb : r.block <;> simp [RootBlock, hrb] at hrr
      next d p s =>
        rcases hrr with ⟨rfl, rfl, _⟩
        have hu := selected_variable_coordinates h a b a 0 0 s r hrb hr
        have hv := selected_variable_coordinates h a' b' a' 0 0 s r hrb hr'
        constructor
        · simpa [sampleOffset, Nat.mod_eq_of_lt ha] using hu.2
        · simpa [sampleOffset, Nat.mod_eq_of_lt ha'] using hv.2
    have ccoord : c.offset = b ∧ c.offset = b' := by
      cases hcb : c.block <;> simp [RootBlock, hcb] at hcc
      next d p s =>
        rcases hcc with ⟨rfl, rfl, _⟩
        have hu := selected_variable_coordinates h a b b 0 0 s c hcb hc
        have hv := selected_variable_coordinates h a' b' b' 0 0 s c hcb hc'
        constructor
        · simpa [sampleOffset, Nat.mod_eq_of_lt hb] using hu.2
        · simpa [sampleOffset, Nat.mod_eq_of_lt hb'] using hv.2
    exact ⟨rcoord.1.symm.trans rcoord.2, ccoord.1.symm.trans ccoord.2⟩

end H4Formal
