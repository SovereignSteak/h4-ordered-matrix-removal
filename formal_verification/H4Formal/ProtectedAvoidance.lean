import H4Formal.ProtectedCells
import H4Formal.FiniteAvoidance

namespace H4Formal

def protectedHit (h : Nat) (cell : PhysicalPosition h × PhysicalPosition h)
    (sample : Nat) : Bool :=
  decide (ProtectedCell h (sample / 2 ^ h) (sample % 2 ^ h) cell.1 cell.2)

theorem protectedHit_unique (h : Nat) (cell : PhysicalPosition h × PhysicalPosition h)
    (s t : Nat) (hs : s < 2 ^ h * 2 ^ h) (ht : t < 2 ^ h * 2 ^ h)
    (hitS : protectedHit h cell s = true) (hitT : protectedHit h cell t = true) : s = t := by
  have hm : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have ha : s / 2 ^ h < 2 ^ h := (Nat.div_lt_iff_lt_mul hm).2 hs
  have hb : s % 2 ^ h < 2 ^ h := Nat.mod_lt s hm
  have ha' : t / 2 ^ h < 2 ^ h := (Nat.div_lt_iff_lt_mul hm).2 ht
  have hb' : t % 2 ^ h < 2 ^ h := Nat.mod_lt t hm
  have hs' : ProtectedCell h (s / 2 ^ h) (s % 2 ^ h) cell.1 cell.2 := by
    simpa [protectedHit] using hitS
  have ht' : ProtectedCell h (t / 2 ^ h) (t % 2 ^ h) cell.1 cell.2 := by
    simpa [protectedHit] using hitT
  obtain ⟨hquot, hrem⟩ := protected_cell_sample_injective h _ _ _ _ ha hb ha' hb'
    cell.1 cell.2 hs' ht'
  have hd := Nat.div_add_mod s (2 ^ h)
  have hd' := Nat.div_add_mod t (2 ^ h)
  rw [hquot, hrem] at hd
  exact hd.symm.trans hd'

theorem protectedHit_count_le_one (h : Nat) (cell : PhysicalPosition h × PhysicalPosition h) :
    (List.range (2 ^ h * 2 ^ h)).countP (protectedHit h cell) ≤ 1 := by
  apply countP_le_one_of_unique _ List.nodup_range
  intro s hs t ht hitS hitT
  exact protectedHit_unique h cell s t (List.mem_range.mp hs) (List.mem_range.mp ht) hitS hitT

/-- Among the `m^2` selections, fewer than `m^2` edits leave an unhit selection. -/
theorem exists_protected_selection (h : Nat)
    (edits : List (PhysicalPosition h × PhysicalPosition h))
    (hsmall : edits.length < 2 ^ h * 2 ^ h) :
    ∃ a b, a < 2 ^ h ∧ b < 2 ^ h ∧
      ∀ cell ∈ edits, ¬ ProtectedCell h a b cell.1 cell.2 := by
  obtain ⟨s, hs, havoid⟩ := exists_unhit_sample
    (List.range (2 ^ h * 2 ^ h)) edits (protectedHit h) 1
    (fun cell _ => protectedHit_count_le_one h cell) (by simpa using hsmall)
  have hm : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hslt := List.mem_range.mp hs
  refine ⟨s / 2 ^ h, s % 2 ^ h, (Nat.div_lt_iff_lt_mul hm).2 hslt, Nat.mod_lt s hm, ?_⟩
  intro cell he
  have hg := havoid cell he
  simpa [protectedHit] using hg

end H4Formal
