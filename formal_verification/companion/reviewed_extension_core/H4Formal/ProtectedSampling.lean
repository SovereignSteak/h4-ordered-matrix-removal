import H4Formal.PhysicalRepresentatives
import Mathlib.Algebra.Group.Fin.Basic

namespace H4Formal

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

abbrev ProtectionSample (h : Nat) := Fin (2 ^ h) × Fin (2 ^ h)

def sampleLeaf (h : Nat) (s : ProtectionSample h) : Fin (2 ^ h) := s.1 + s.2

def rigidPosition (h : Nat) : PhysicalPosition h → Bool
  | .inl _ => true
  | .inr (.inl (d, _, _)) => d.val == 0
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr _)) => true

def rowSelected (h : Nat) (s : ProtectionSample h) (r : PhysicalPosition h) : Prop :=
  physicalCoordinate h r = if rigidPosition h r = true then s.1 else sampleLeaf h s

def colSelected (h : Nat) (s : ProtectionSample h) (c : PhysicalPosition h) : Prop :=
  physicalCoordinate h c = if rigidPosition h c = true then s.2 else sampleLeaf h s

def IsProtected (h : Nat) (s : ProtectionSample h)
    (cell : PhysicalPosition h × PhysicalPosition h) : Prop :=
  rowSelected h s cell.1 ∧ colSelected h s cell.2 ∧
    (rigidPosition h cell.1 = true ∨ rigidPosition h cell.2 = true)

theorem protected_sample_unique (h : Nat) (s t : ProtectionSample h)
    (cell : PhysicalPosition h × PhysicalPosition h)
    (hs : IsProtected h s cell) (ht : IsProtected h t cell) : s = t := by
  rcases hs with ⟨hsr, hsc, helig⟩
  rcases ht with ⟨htr, htc, _⟩
  have hr := hsr.symm.trans htr
  have hc := hsc.symm.trans htc
  by_cases er : rigidPosition h cell.1 = true
  · have ha : s.1 = t.1 := by simpa only [if_pos er] using hr
    by_cases ec : rigidPosition h cell.2 = true
    · exact Prod.ext ha (by simpa only [if_pos ec] using hc)
    · have hz : s.1 + s.2 = t.1 + t.2 := by
        simpa only [if_neg ec, sampleLeaf] using hc
      apply Prod.ext ha
      exact add_left_cancel (by simpa only [ha] using hz)
  · have ec : rigidPosition h cell.2 = true := helig.resolve_left er
    have hb : s.2 = t.2 := by simpa only [if_pos ec] using hc
    have hz : s.1 + s.2 = t.1 + t.2 := by
      simpa only [if_neg er, sampleLeaf] using hr
    apply Prod.ext _ hb
    exact add_right_cancel (by simpa only [hb] using hz)

def editCells (h : Nat) (a b : PhysicalMatrix h) :
    Finset (PhysicalPosition h × PhysicalPosition h) :=
  Finset.univ.filter (fun cell => a cell.1 cell.2 ≠ b cell.1 cell.2)

def editCount (h : Nat) (a b : PhysicalMatrix h) : Nat := (editCells h a b).card

def ProtectedClean (h : Nat) (s : ProtectionSample h) (matrix : PhysicalMatrix h) : Prop :=
  ∀ cell, IsProtected h s cell →
    matrix cell.1 cell.2 = physicalMatrix h false cell.1 cell.2

theorem exists_protected_clean_sample (h : Nat) (matrix : PhysicalMatrix h)
    (hedits : editCount h (physicalMatrix h false) matrix < (2 ^ h) ^ 2) :
    ∃ s : ProtectionSample h, ProtectedClean h s matrix := by
  classical
  by_contra hn
  have hbad : ∀ s : ProtectionSample h,
      ∃ cell, cell ∈ editCells h (physicalMatrix h false) matrix ∧ IsProtected h s cell := by
    intro s
    have hs : ¬ ProtectedClean h s matrix := fun hp => hn ⟨s, hp⟩
    simp only [ProtectedClean, not_forall, _root_.not_imp] at hs
    obtain ⟨cell, hp, hne⟩ := hs
    exact ⟨cell, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hne⟩, hp⟩
  choose cell hmem hprotect using hbad
  let f (s : ProtectionSample h) :
      { c // c ∈ editCells h (physicalMatrix h false) matrix } := ⟨cell s, hmem s⟩
  have hf : Function.Injective f := by
    intro s t he
    have he' : cell s = cell t := congrArg Subtype.val he
    apply protected_sample_unique h s t (cell s) (hprotect s)
    rw [he']
    exact hprotect t
  have hcard := Fintype.card_le_of_injective f hf
  simp only [ProtectionSample, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe] at hcard
  dsimp [editCount] at hedits
  rw [Nat.pow_two] at hedits
  omega

end H4Formal
