import H4Formal.PhysicalHost

namespace H4Formal

def modesAt (i : Nat) : List Mode :=
  [⟨.v, i, 0, .plus⟩, ⟨.v, i, 0, .minus⟩,
   ⟨.w, i, 0, .plus⟩, ⟨.w, i, 1, .plus⟩,
   ⟨.w, i, 0, .minus⟩, ⟨.w, i, 1, .minus⟩]

def anchorsAt (i : Nat) : List Block :=
  (modesAt i).flatMap (fun m => [.anchor m 1, .anchor m 2])

def anchorBlocks (h : Nat) : List Block :=
  (List.range h).flatMap (fun i => anchorsAt (i + 1))

def signedBlocksAt (d : Nat) : List Block :=
  (List.range (2 ^ d)).flatMap (fun p => [.variable d p .plus, .variable d p .minus])

def variableBlocks (h : Nat) : List Block :=
  (List.range h).flatMap signedBlocksAt ++
    (List.range (2 ^ h)).map (fun p => .variable h p .leaf)

def allBlocks (h : Nat) : List Block := anchorBlocks h ++ variableBlocks h ++ [.dummy]

def weightedSize (h : Nat) (bs : List Block) : Nat := (bs.map (blockSize h)).sum

def physicalPairs (h : Nat) : List (Block × Nat) :=
  (allBlocks h).flatMap (fun b => (List.range (blockSize h b)).map (fun k => (b, k)))

theorem weightedSize_append (h : Nat) (xs ys : List Block) :
    weightedSize h (xs ++ ys) = weightedSize h xs + weightedSize h ys := by
  simp [weightedSize, List.sum_append_nat]

theorem weightedSize_flatMap (h : Nat) (xs : List α) (f : α → List Block) :
    weightedSize h (xs.flatMap f) = (xs.map (fun x => weightedSize h (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, weightedSize_append, ih]

theorem mem_modesAt (i : Nat) (m : Mode) :
    m ∈ modesAt i ↔ m.depth = i ∧
      (m.sign = .plus ∨ m.sign = .minus) ∧
      (match m.family with | .v => m.parity = 0 | .w => m.parity < 2) := by
  rcases m with ⟨f, d, p, s⟩
  cases f <;> cases s <;> simp [modesAt, Mode.mk.injEq] <;> omega

theorem mem_anchorsAt (i : Nat) (b : Block) :
    b ∈ anchorsAt i ↔ ∃ m g, b = .anchor m g ∧ m ∈ modesAt i ∧ (g = 1 ∨ g = 2) := by
  simp [anchorsAt]
  constructor
  · rintro ⟨m, hm, he | he⟩
    · exact ⟨m, 1, he, hm, Or.inl rfl⟩
    · exact ⟨m, 2, he, hm, Or.inr rfl⟩
  · rintro ⟨m, g, rfl, hm, rfl | rfl⟩ <;> exact ⟨m, hm, by simp⟩

theorem mem_anchorBlocks (h : Nat) (b : Block) :
    b ∈ anchorBlocks h ↔ ∃ m g, b = .anchor m g ∧ ValidMode h m ∧ (g = 1 ∨ g = 2) := by
  simp only [anchorBlocks, List.mem_flatMap, List.mem_range, mem_anchorsAt]
  constructor
  · rintro ⟨i, hi, m, g, rfl, hm, hg⟩
    rcases (mem_modesAt _ _).1 hm with ⟨hd, hs, hp⟩
    exact ⟨m, g, rfl, by unfold ValidMode; exact ⟨by omega, by omega, hs, hp⟩, hg⟩
  · rintro ⟨m, g, rfl, hm, hg⟩
    rcases hm with ⟨hi, hih, hs, hp⟩
    refine ⟨m.depth - 1, by omega, m, g, rfl, ?_, hg⟩
    exact (mem_modesAt _ _).2 ⟨by omega, hs, hp⟩

theorem mem_signedBlocksAt (d : Nat) (b : Block) :
    b ∈ signedBlocksAt d ↔ ∃ p s, b = .variable d p s ∧ p < 2 ^ d ∧
      (s = .plus ∨ s = .minus) := by
  simp [signedBlocksAt]
  constructor
  · rintro ⟨p, hp, he | he⟩
    · exact ⟨p, .plus, he, hp, Or.inl rfl⟩
    · exact ⟨p, .minus, he, hp, Or.inr rfl⟩
  · rintro ⟨p, s, rfl, hp, rfl | rfl⟩ <;> exact ⟨p, hp, by simp⟩

theorem mem_variableBlocks (h : Nat) (b : Block) :
    b ∈ variableBlocks h ↔ ∃ d p s, b = .variable d p s ∧ ValidBlock h (.variable d p s) := by
  simp only [variableBlocks, List.mem_append, List.mem_flatMap, List.mem_range,
    mem_signedBlocksAt, List.mem_map]
  constructor
  · rintro (⟨d, hd, p, s, rfl, hp, hs⟩ | ⟨p, hp, rfl⟩)
    · refine ⟨d, p, s, rfl, by simp [ValidBlock, hs]; omega⟩
    · exact ⟨h, p, .leaf, rfl, by simp [ValidBlock, hp]⟩
  · rintro ⟨d, p, s, rfl, hd, hp, hs⟩
    by_cases he : d = h
    · subst d
      have he : s = .leaf := by simpa using hs
      subst s
      exact Or.inr ⟨p, hp, rfl⟩
    · left
      exact ⟨d, by omega, p, s, rfl, hp, by simpa [he] using hs⟩

theorem mem_allBlocks (h : Nat) (b : Block) : b ∈ allBlocks h ↔ ValidBlock h b := by
  simp only [allBlocks, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    mem_anchorBlocks, mem_variableBlocks]
  cases b <;> simp [ValidBlock] <;> grind

theorem mem_physicalPairs (h : Nat) (b : Block) (k : Nat) :
    (b, k) ∈ physicalPairs h ↔ ValidBlock h b ∧ k < blockSize h b := by
  simp [physicalPairs, mem_allBlocks]

theorem anchorsAt_weight (h i : Nat) : weightedSize h (anchorsAt i) = 12 * 2 ^ h := by
  simp [weightedSize, anchorsAt, modesAt, blockSize]
  omega

theorem anchorBlocks_weight (h : Nat) : weightedSize h (anchorBlocks h) = 12 * h * 2 ^ h := by
  rw [anchorBlocks, weightedSize_flatMap]
  simp [anchorsAt_weight, List.map_const', Nat.mul_comm, Nat.mul_left_comm]

theorem pow_split (h d : Nat) (hd : d ≤ h) : 2 ^ d * 2 ^ (h - d) = 2 ^ h := by
  rw [← Nat.pow_add, Nat.add_sub_of_le hd]

theorem signedBlocksAt_weight (h d : Nat) (hd : d ≤ h) :
    weightedSize h (signedBlocksAt d) = 2 * 2 ^ h := by
  rw [signedBlocksAt, weightedSize_flatMap]
  simp [weightedSize, blockSize, List.map_const']
  rw [Nat.mul_add, pow_split h d hd]
  omega

theorem variableBlocks_weight (h : Nat) : weightedSize h (variableBlocks h) = (2 * h + 1) * 2 ^ h := by
  rw [variableBlocks, weightedSize_append, weightedSize_flatMap]
  have hi : ((List.range h).map (fun d => weightedSize h (signedBlocksAt d))) =
      List.replicate h (2 * 2 ^ h) := by
    have hw : ((List.range h).map (fun d => weightedSize h (signedBlocksAt d))) =
        List.replicate (List.range h).length (2 * 2 ^ h) := by
      apply List.map_eq_replicate_iff.mpr
      intro d hd
      exact signedBlocksAt_weight h d (Nat.le_of_lt (List.mem_range.mp hd))
    simpa using hw
  rw [hi]
  simp [weightedSize, List.map_map, Function.comp_def, blockSize, List.map_const', Nat.add_mul,
    Nat.mul_assoc, Nat.mul_comm]

theorem allBlocks_weight (h : Nat) : weightedSize h (allBlocks h) = (14 * h + 2) * 2 ^ h := by
  simp only [allBlocks, weightedSize_append, anchorBlocks_weight, variableBlocks_weight]
  simp only [weightedSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, blockSize]
  simp [Nat.add_mul, Nat.mul_assoc]
  omega

theorem physicalPairs_length (h : Nat) : (physicalPairs h).length = (14 * h + 2) * 2 ^ h := by
  rw [physicalPairs, List.length_flatMap]
  simpa [weightedSize] using allBlocks_weight h

theorem nodup_map_injective {α : Type u} {β : Type v} (xs : List α) (f : α → β)
    (hn : xs.Nodup) (hi : ∀ x y, f x = f y → x = y) : (xs.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact hn.imp (fun hne he => hne (hi _ _ he))

theorem nodup_flatMap_disjoint {α : Type u} {β : Type v} (xs : List α) (f : α → List β)
    (hn : xs.Nodup) (hf : ∀ x ∈ xs, (f x).Nodup)
    (hd : ∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → ∀ a ∈ f x, ∀ b ∈ f y, a ≠ b) :
    (xs.flatMap f).Nodup := by
  apply List.pairwise_flatMap.mpr
  exact ⟨hf, hn.imp_of_mem (fun hx hy hxy => hd _ hx _ hy hxy)⟩

theorem modesAt_nodup (i : Nat) : (modesAt i).Nodup := by
  simp [modesAt, List.nodup_cons]

theorem anchorsAt_nodup (i : Nat) : (anchorsAt i).Nodup := by
  apply nodup_flatMap_disjoint _ _ (modesAt_nodup i)
  · intro m _; simp [List.nodup_cons]
  · intro m _ n _ hne a ha b hb he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Block.anchor.injEq] at he <;> exact hne he.1

theorem anchorBlocks_nodup (h : Nat) : (anchorBlocks h).Nodup := by
  apply nodup_flatMap_disjoint _ _ List.nodup_range
  · intro i _; exact anchorsAt_nodup _
  · intro i _ j _ hne a ha b hb he
    rcases (mem_anchorsAt _ _).1 ha with ⟨m, g, rfl, hm, _⟩
    rcases (mem_anchorsAt _ _).1 hb with ⟨n, k, rfl, hn, _⟩
    have hd := (mem_modesAt _ _).1 hm
    have he' := (mem_modesAt _ _).1 hn
    have me := (Block.anchor.inj he).1
    have := congrArg Mode.depth me
    exact hne (by omega)

theorem signedBlocksAt_nodup (d : Nat) : (signedBlocksAt d).Nodup := by
  apply nodup_flatMap_disjoint _ _ List.nodup_range
  · intro p _; simp [List.nodup_cons]
  · intro p _ q _ hne a ha b hb he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [Block.variable.injEq] at he <;> exact hne he.2.1

theorem variableBlocks_nodup (h : Nat) : (variableBlocks h).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply nodup_flatMap_disjoint _ _ List.nodup_range
    · intro d _; exact signedBlocksAt_nodup d
    · intro d _ e _ hne a ha b hb he
      rcases (mem_signedBlocksAt _ _).1 ha with ⟨p, s, rfl, _⟩
      rcases (mem_signedBlocksAt _ _).1 hb with ⟨q, t, rfl, _⟩
      exact hne (Block.variable.inj he).1
  · apply nodup_map_injective _ _ List.nodup_range
    intro p q he; exact (Block.variable.inj he).2.1
  · intro a ha b hb he
    rcases List.mem_flatMap.mp ha with ⟨d, hd, ha⟩
    rcases (mem_signedBlocksAt _ _).1 ha with ⟨p, s, rfl, _⟩
    rcases List.mem_map.mp hb with ⟨q, _, rfl⟩
    have := (Block.variable.inj he).1
    have := List.mem_range.mp hd
    omega

theorem allBlocks_nodup (h : Nat) : (allBlocks h).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨anchorBlocks_nodup h, variableBlocks_nodup h, ?_⟩,
    by simp, ?_⟩
  · intro a ha b hb he
    rcases (mem_anchorBlocks _ _).1 ha with ⟨m, g, rfl, _⟩
    rcases (mem_variableBlocks _ _).1 hb with ⟨d, p, s, rfl, _⟩
    cases he
  · intro a ha b hb he
    have hb : b = .dummy := by simpa using hb
    rcases List.mem_append.mp ha with ha | ha
    · rcases (mem_anchorBlocks _ _).1 ha with ⟨m, g, rfl, _⟩; simp_all
    · rcases (mem_variableBlocks _ _).1 ha with ⟨d, p, s, rfl, _⟩; simp_all

theorem physicalPairs_nodup (h : Nat) : (physicalPairs h).Nodup := by
  apply nodup_flatMap_disjoint _ _ (allBlocks_nodup h)
  · intro b _; apply nodup_map_injective _ _ List.nodup_range
    intro i j he; exact (Prod.mk.inj he).2
  · intro b _ c _ hne x hx y hy he
    rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨j, _, rfl⟩
    exact hne (Prod.mk.inj he).1

def indexedPosition (h : Nat) (i : Fin ((14 * h + 2) * 2 ^ h)) : PhysicalPosition h :=
  let k : Fin (physicalPairs h).length := ⟨i.val, by rw [physicalPairs_length]; exact i.isLt⟩
  let x := (physicalPairs h).get k
  have hx : x ∈ physicalPairs h := List.get_mem _ _
  have hv := (mem_physicalPairs h x.1 x.2).1 hx
  ⟨x.1, hv.1, x.2, hv.2⟩

theorem physicalPosition_ext {h : Nat} (x y : PhysicalPosition h)
    (hb : x.block = y.block) (ho : x.offset = y.offset) : x = y := by
  cases x; cases y
  cases hb; cases ho
  rfl

theorem indexedPosition_injective (h : Nat)
    (i j : Fin ((14 * h + 2) * 2 ^ h)) (he : indexedPosition h i = indexedPosition h j) : i = j := by
  apply Fin.ext
  have hb := congrArg PhysicalPosition.block he
  have ho := congrArg PhysicalPosition.offset he
  have hi : i.val < (physicalPairs h).length := by rw [physicalPairs_length]; exact i.isLt
  have hj : j.val < (physicalPairs h).length := by rw [physicalPairs_length]; exact j.isLt
  have hx : (physicalPairs h)[i.val] = (physicalPairs h)[j.val] := Prod.ext hb ho
  apply List.getElem?_inj hi (physicalPairs_nodup h)
  simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using congrArg some hx

theorem indexedPosition_surjective (h : Nat) (p : PhysicalPosition h) :
    ∃ i, indexedPosition h i = p := by
  have hm : (p.block, p.offset) ∈ physicalPairs h :=
    (mem_physicalPairs h p.block p.offset).2 ⟨p.valid, p.offset_lt⟩
  rcases List.mem_iff_get.mp hm with ⟨k, hk⟩
  let i : Fin ((14 * h + 2) * 2 ^ h) := ⟨k.val, by rw [← physicalPairs_length]; exact k.isLt⟩
  refine ⟨i, ?_⟩
  apply physicalPosition_ext
  · exact congrArg Prod.fst hk
  · exact congrArg Prod.snd hk

noncomputable def positionIndex (h : Nat) (p : PhysicalPosition h) : Fin ((14 * h + 2) * 2 ^ h) :=
  Classical.choose (indexedPosition_surjective h p)

theorem indexedPosition_positionIndex (h : Nat) (p : PhysicalPosition h) :
    indexedPosition h (positionIndex h p) = p := Classical.choose_spec (indexedPosition_surjective h p)

theorem positionIndex_indexedPosition (h : Nat) (i : Fin ((14 * h + 2) * 2 ^ h)) :
    positionIndex h (indexedPosition h i) = i := by
  apply indexedPosition_injective h
  exact indexedPosition_positionIndex h _

/-- Finite indexing equipped with the pullback of the physical DFS relation. -/
def indexedHost (h : Nat) (repair : Bool := false) :
    OrderedMatrix (Fin ((14 * h + 2) * 2 ^ h)) (Fin ((14 * h + 2) * 2 ^ h)) where
  value i j := (physicalHost h repair).value (indexedPosition h i) (indexedPosition h j)
  rowBefore i j := physicalBefore .row (indexedPosition h i) (indexedPosition h j)
  colBefore i j := physicalBefore .column (indexedPosition h i) (indexedPosition h j)

theorem indexed_copy_iff (h : Nat) (repair : Bool)
    (r c : Fin 4 → Fin ((14 * h + 2) * 2 ^ h)) :
    MatrixCopy (indexedHost h repair) r c ↔
      MatrixCopy (physicalHost h repair) (fun i => indexedPosition h (r i))
        (fun i => indexedPosition h (c i)) := Iff.rfl

theorem indexed_free_iff (h : Nat) (repair : Bool) :
    PatternFree (indexedHost h repair) ↔ PatternFree (physicalHost h repair) := by
  constructor
  · intro hf r c hc
    apply hf (fun i => positionIndex h (r i)) (fun i => positionIndex h (c i))
    simpa only [indexed_copy_iff, indexedPosition_positionIndex] using hc
  · intro hf r c hc
    exact hf _ _ ((indexed_copy_iff h repair r c).1 hc)

end H4Formal
