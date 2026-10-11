import H4Formal.GeneralPhysicalCompression
import H4Formal.FiniteMultiplicity

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

def BlockFiber (h : Nat) (b : Block) :=
  { p : PhysicalPosition h // physicalBlock h p = b }

instance (h : Nat) (b : Block) : Fintype (BlockFiber h b) :=
  inferInstanceAs (Fintype { p : PhysicalPosition h // physicalBlock h p = b })

theorem physicalOffset_lt_multiplicity (h : Nat) (p : PhysicalPosition h) :
    physicalOffset h p < multiplicity h (physicalBlock h p) := by
  rcases p with ⟨d, mode, group, offset⟩ | (⟨d, sign, position⟩ | (leaf | offset))
  · exact offset.isLt
  · fin_cases sign <;> exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · exact Nat.zero_lt_one
  · exact offset.isLt

theorem valid_block_offset_realization (h : Nat) (b : Block)
    (hv : validBlock h b = true) (offset : Fin (multiplicity h b)) :
    ∃ p : PhysicalPosition h, physicalBlock h p = b ∧ physicalOffset h p = offset.val := by
  cases b with
  | anchor mode group =>
      have hb := hv
      simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq,
        Bool.or_eq_true, beq_iff_eq] at hb
      have hd : 1 ≤ mode.depth ∧ mode.depth ≤ h := hb.1.1
      have hg : group = 1 ∨ group = 2 := hb.1.2
      have hm := mode_code_le_five_of_allowed mode hb.2
      refine ⟨.inl (⟨mode.depth - 1, by omega⟩,
        ⟨modeCode mode, by omega⟩, ⟨group - 1, by omega⟩, offset), ?_, rfl⟩
      simp only [physicalBlock]
      rw [Nat.sub_add_cancel hd.1, mode_code_roundtrip mode hb.2,
        Nat.sub_add_cancel (by omega : 1 ≤ group)]
  | «variable» d p sign =>
      have hs := valid_variable_sign hv
      have hn := valid_variable_node hv
      have hd : d ≤ h := hs.1
      by_cases ht : d = h
      · have he : sign = .leaf := by simpa only [if_pos ht] using hs.2
        subst d
        subst sign
        refine ⟨.inr (.inr (.inl ⟨p, hn⟩)), rfl, ?_⟩
        have ho : offset.val < 1 := offset.isLt
        change 0 = offset.val
        omega
      · have hsign : sign = .plus ∨ sign = .minus := by
          simpa only [if_neg ht] using hs.2
        rcases hsign with rfl | rfl
        all_goals
          have ho : offset.val < 2 ^ (h - d) := offset.isLt
          have hp : p * 2 ^ (h - d) + offset.val < 2 ^ h := by
            rw [level_factor h d hd]
            have hl := Nat.mul_le_mul_right (2 ^ (h - d)) (Nat.succ_le_of_lt hn)
            rw [Nat.succ_mul] at hl
            omega
        · refine ⟨.inr (.inl (⟨d, by omega⟩, 0, ⟨p * 2 ^ (h - d) + offset.val, hp⟩)), ?_, ?_⟩
          · simp [physicalBlock, Nat.add_div, Nat.div_eq_of_lt ho, Nat.mod_eq_of_lt ho, ho]
          · simp [physicalOffset, Nat.mod_eq_of_lt ho]
        · refine ⟨.inr (.inl (⟨d, by omega⟩, 1, ⟨p * 2 ^ (h - d) + offset.val, hp⟩)), ?_, ?_⟩
          · simp [physicalBlock, Nat.add_div, Nat.div_eq_of_lt ho, Nat.mod_eq_of_lt ho, ho]
          · simp [physicalOffset, Nat.mod_eq_of_lt ho]
  | dummy => exact ⟨.inr (.inr (.inr offset)), rfl, rfl⟩

noncomputable def blockFiberEquiv (h : Nat) (b : Block) (hv : validBlock h b = true) :
    BlockFiber h b ≃ Fin (multiplicity h b) := by
  let f (p : BlockFiber h b) : Fin (multiplicity h b) :=
    ⟨physicalOffset h p.val, by simpa only [p.property] using physicalOffset_lt_multiplicity h p.val⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    apply Subtype.ext
    apply physicalBlockOffset_injective h
    exact Prod.ext (p.property.trans q.property.symm) (congrArg Fin.val he)
  · intro offset
    obtain ⟨p, hb, ho⟩ := valid_block_offset_realization h b hv offset
    exact ⟨⟨p, hb⟩, Fin.ext ho⟩

theorem blockFiber_card (h : Nat) (b : Block) (hv : validBlock h b = true) :
    Fintype.card (BlockFiber h b) = multiplicity h b := by
  rw [Fintype.card_congr (blockFiberEquiv h b hv), Fintype.card_fin]

def PhysicalPatternLifts {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (rows cols : Fin k → Block) :=
  { rc : (Fin k → PhysicalPosition h) × (Fin k → PhysicalPosition h) //
    IsPhysicalPatternCopy h patt (physicalMatrix h repair) rc.1 rc.2 ∧
      (∀ i, physicalBlock h (rc.1 i) = rows i) ∧
      (∀ j, physicalBlock h (rc.2 j) = cols j) }

noncomputable instance {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (rows cols : Fin k → Block) :
    Fintype (PhysicalPatternLifts h repair patt rows cols) := by
  unfold PhysicalPatternLifts
  exact Fintype.ofFinite _

def physicalPatternLiftsEquiv {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (rows cols : Fin k → Block)
    (hc : IsValidPatternCopy h repair patt rows cols) :
    PhysicalPatternLifts h repair patt rows cols ≃
      (∀ i, BlockFiber h (rows i)) × (∀ j, BlockFiber h (cols j)) where
  toFun := fun x => (fun i => ⟨x.val.1 i, x.property.2.1 i⟩,
    fun j => ⟨x.val.2 j, x.property.2.2 j⟩)
  invFun := fun x => ⟨(fun i => (x.1 i).val, fun j => (x.2 j).val), by
    refine ⟨⟨?_, ?_, ?_⟩, fun i => (x.1 i).property, fun j => (x.2 j).property⟩
    · intro i j hij
      apply Or.inr
      rw [(x.1 i).property, (x.1 j).property]
      exact hc.2.1 i j hij
    · intro i j hij
      apply Or.inr
      rw [(x.2 i).property, (x.2 j).property]
      exact hc.2.2.1 i j hij
    · intro i j
      simpa only [physicalMatrix, (x.1 i).property, (x.2 j).property] using hc.2.2.2 i j⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem physical_pattern_lifts_card {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (rows cols : Fin k → Block)
    (hc : IsValidPatternCopy h repair patt rows cols) :
    Fintype.card (PhysicalPatternLifts h repair patt rows cols) =
      (∏ i, multiplicity h (rows i)) * (∏ j, multiplicity h (cols j)) := by
  rw [Fintype.card_congr (physicalPatternLiftsEquiv h repair patt rows cols hc),
    Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    exact blockFiber_card h (rows i)
      (hc.1 _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  · apply Finset.prod_congr rfl
    intro i _
    exact blockFiber_card h (cols i)
      (hc.1 _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))

end H4Formal
