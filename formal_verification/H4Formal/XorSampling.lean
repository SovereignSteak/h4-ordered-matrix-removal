import H4Formal.PhysicalHost

namespace H4Formal

def sampleLeaf (a b : Nat) : Nat := a ^^^ b
def sampleNode (h d a b : Nat) : Nat := (a ^^^ b) / 2 ^ (h - d)
def sampleOffset (h d a : Nat) : Nat := a % 2 ^ (h - d)

theorem xor_right_cancel (a b c : Nat) (he : a ^^^ c = b ^^^ c) : a = b := by
  have hx := congrArg (fun x => x ^^^ c) he
  simpa [Nat.xor_assoc] using hx

theorem xor_left_cancel (a b c : Nat) (he : a ^^^ b = a ^^^ c) : b = c := by
  apply xor_right_cancel b c a
  simpa [Nat.xor_comm] using he

theorem sampleNode_lt (h d a b : Nat) (hd : d ≤ h)
    (ha : a < 2 ^ h) (hb : b < 2 ^ h) : sampleNode h d a b < 2 ^ d := by
  have hp : 0 < 2 ^ (h - d) := Nat.pow_pos (by decide)
  apply (Nat.div_lt_iff_lt_mul hp).2
  have hsum : d + (h - d) = h := by omega
  rw [← Nat.pow_add, hsum]
  exact Nat.xor_lt_two_pow ha hb

theorem sampleOffset_lt (h d a : Nat) : sampleOffset h d a < 2 ^ (h - d) :=
  Nat.mod_lt a (Nat.pow_pos (by decide))

/-- A variable row and a marker column determine both sample coordinates. -/
theorem sample_row_marker_injective (h d a b a' b' : Nat)
    (hnode : sampleNode h d a b = sampleNode h d a' b')
    (hoffset : sampleOffset h d a = sampleOffset h d a') (hb : b = b') :
    a = a' ∧ b = b' := by
  subst b'
  unfold sampleNode at hnode
  rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow] at hnode
  have hquot := xor_right_cancel _ _ _ hnode
  have he : a = a' := by
    have hdecomp := Nat.div_add_mod a (2 ^ (h - d))
    have hdecomp' := Nat.div_add_mod a' (2 ^ (h - d))
    unfold sampleOffset at hoffset
    rw [hquot, hoffset] at hdecomp
    exact hdecomp.symm.trans hdecomp'
  exact ⟨he, rfl⟩

/-- A marker row and a variable column determine both sample coordinates. -/
theorem sample_marker_column_injective (h d a b a' b' : Nat) (ha : a = a')
    (hnode : sampleNode h d a b = sampleNode h d a' b')
    (hoffset : sampleOffset h d b = sampleOffset h d b') :
    a = a' ∧ b = b' := by
  subst a'
  unfold sampleNode at hnode
  rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow] at hnode
  have hquot := xor_left_cancel _ _ _ hnode
  have he : b = b' := by
    have hdecomp := Nat.div_add_mod b (2 ^ (h - d))
    have hdecomp' := Nat.div_add_mod b' (2 ^ (h - d))
    unfold sampleOffset at hoffset
    rw [hquot, hoffset] at hdecomp
    exact hdecomp.symm.trans hdecomp'
  exact ⟨rfl, he⟩

theorem sampleNode_parent (h i a b : Nat) (hi : 1 ≤ i) (hih : i ≤ h) :
    sampleNode h i a b / 2 = sampleNode h (i - 1) a b := by
  unfold sampleNode
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  congr 2
  omega

theorem sampleNode_root (h a b : Nat) (ha : a < 2 ^ h) (hb : b < 2 ^ h) :
    sampleNode h 0 a b = 0 := by
  unfold sampleNode
  simp only [Nat.sub_zero]
  exact Nat.div_eq_of_lt (Nat.xor_lt_two_pow ha hb)

theorem sampleNode_leaf (h a b : Nat) : sampleNode h h a b = sampleLeaf a b := by
  simp [sampleNode, sampleLeaf]

theorem sampleOffset_leaf (h a : Nat) : sampleOffset h h a = 0 := by
  simp [sampleOffset, Nat.mod_one]

end H4Formal
