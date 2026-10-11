import H4Formal.HostSize

namespace H4Formal

theorem finRange_mem (n : Nat) (i : Fin n) : i ∈ List.finRange n := by
  simp [List.finRange, List.mem_ofFn]

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.nodup_cons]
      constructor
      · simp [List.mem_map]; intro i _ he; have := congrArg Fin.val he; simp at this
      · apply nodup_map_injective _ _ ih
        intro i j he
        apply Fin.ext
        have := congrArg Fin.val he
        simpa using this

def dummyPosition (h : Nat) (i : Fin (2 ^ h)) : PhysicalPosition h :=
  ⟨.dummy, True.intro, i.val, i.isLt⟩

def leafPosition (h : Nat) (p : Fin (2 ^ h)) : PhysicalPosition h :=
  ⟨.variable h p.val .leaf, by simp [ValidBlock],
    0, by simp [blockSize]⟩

def canonicalEdits (h : Nat) : List (PhysicalPosition h × PhysicalPosition h) :=
  (List.finRange (2 ^ h)).flatMap (fun i =>
    (List.finRange (2 ^ h)).map (fun p => (dummyPosition h i, leafPosition h p)))

theorem canonicalEdits_length (h : Nat) : (canonicalEdits h).length = 2 ^ h * 2 ^ h := by
  simp [canonicalEdits, List.length_flatMap, List.map_const']

theorem canonicalEdits_nodup (h : Nat) : (canonicalEdits h).Nodup := by
  apply nodup_flatMap_disjoint _ _ (finRange_nodup _)
  · intro i _
    apply nodup_map_injective _ _ (finRange_nodup _)
    intro p q he
    have hb := congrArg PhysicalPosition.block (Prod.mk.inj he).2
    apply Fin.ext
    exact (Block.variable.inj hb).2.1
  · intro i _ j _ hne x hx y hy he
    rcases List.mem_map.mp hx with ⟨p, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨q, _, rfl⟩
    have ho := congrArg PhysicalPosition.offset (Prod.mk.inj he).1
    exact hne (Fin.ext ho)

theorem canonicalEdits_covers (h : Nat) (r c : PhysicalPosition h)
    (he : repairedValue h r.block c.block ≠ hostValue h r.block c.block) :
    (r, c) ∈ canonicalEdits h := by
  have hr : r.block = .dummy := by
    apply Classical.byContradiction
    intro hn
    exact he (repaired_unchanged_outside_dummy h r.block c.block hn)
  have hc : isTerminalLeaf h c.block = true := by
    apply Classical.byContradiction
    intro hn
    simp [repairedValue, hr, hn] at he
  cases hcb : c.block with
  | anchor m g => simp [isTerminalLeaf, hcb] at hc
  | dummy => simp [isTerminalLeaf, hcb] at hc
  | «variable» d p s =>
      cases s <;> simp [isTerminalLeaf, hcb] at hc
      next =>
        subst d
        have hv := c.valid
        simp [hcb, ValidBlock] at hv
        have ho : c.offset = 0 := by
          have ht := c.offset_lt
          simp [hcb, blockSize] at ht
          omega
        let i : Fin (2 ^ h) := ⟨r.offset, by simpa [hr, blockSize] using r.offset_lt⟩
        let q : Fin (2 ^ h) := ⟨p, hv⟩
        have re : dummyPosition h i = r := physicalPosition_ext _ _ hr.symm rfl
        have ce : leafPosition h q = c := physicalPosition_ext _ _ hcb.symm ho.symm
        unfold canonicalEdits
        apply List.mem_flatMap.mpr
        refine ⟨i, finRange_mem _ _, List.mem_map.mpr ⟨q, finRange_mem _ _, ?_⟩⟩
        exact Prod.ext re ce

theorem canonicalEdits_exact (h : Nat) (r c : PhysicalPosition h) :
    (r, c) ∈ canonicalEdits h ↔
      repairedValue h r.block c.block ≠ hostValue h r.block c.block := by
  constructor
  · intro hm
    rcases List.mem_flatMap.mp hm with ⟨i, _, hm⟩
    rcases List.mem_map.mp hm with ⟨p, _, he⟩
    have hr := congrArg (fun x => x.1.block) he
    have hc := congrArg (fun x => x.2.block) he
    simp [dummyPosition, leafPosition] at hr hc
    rw [← hr, ← hc, repaired_dummy_terminal, original_dummy_terminal]
    decide
  · exact canonicalEdits_covers h r c

end H4Formal
