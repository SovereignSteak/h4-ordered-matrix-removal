import H4Formal.CanonicalEdits
import H4Formal.TerminalCount

namespace H4Formal

def listProduct (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

theorem listProduct_length (xs : List α) (ys : List β) :
    (listProduct xs ys).length = xs.length * ys.length := by
  simp [listProduct, List.length_flatMap, List.map_const']

theorem mem_listProduct (xs : List α) (ys : List β) (x : α) (y : β) :
    (x, y) ∈ listProduct xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp [listProduct]

theorem listProduct_nodup (xs : List α) (ys : List β) (hx : xs.Nodup) (hy : ys.Nodup) :
    (listProduct xs ys).Nodup := by
  apply nodup_flatMap_disjoint _ _ hx
  · intro x _
    apply nodup_map_injective _ _ hy
    intro y z he
    exact (Prod.mk.inj he).2
  · intro x _ y _ hne a ha b hb he
    rcases List.mem_map.mp ha with ⟨u, _, rfl⟩
    rcases List.mem_map.mp hb with ⟨v, _, rfl⟩
    exact hne (Prod.mk.inj he).1

def listFour (xs ys zs ws : List α) : List (Fin 4 → α) :=
  (listProduct (listProduct xs ys) (listProduct zs ws)).map (fun p =>
    four p.1.1 p.1.2 p.2.1 p.2.2)

theorem four_eta (r : Fin 4 → α) : four (r 0) (r 1) (r 2) (r 3) = r := by
  funext i
  have hi := i.isLt
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | n + 4 => omega

theorem listFour_length (xs ys zs ws : List α) :
    (listFour xs ys zs ws).length = xs.length * ys.length * zs.length * ws.length := by
  simp [listFour, listProduct_length, Nat.mul_assoc]

theorem mem_listFour (xs ys zs ws : List α) (r : Fin 4 → α) :
    r ∈ listFour xs ys zs ws ↔ r 0 ∈ xs ∧ r 1 ∈ ys ∧ r 2 ∈ zs ∧ r 3 ∈ ws := by
  constructor
  · intro hr
    rcases List.mem_map.mp hr with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hm, he⟩
    rcases (mem_listProduct _ _ _ _).1 hm with ⟨hab, hcd⟩
    rcases (mem_listProduct _ _ _ _).1 hab with ⟨ha, hb⟩
    rcases (mem_listProduct _ _ _ _).1 hcd with ⟨hc, hd⟩
    subst r
    simpa [four] using And.intro ha (And.intro hb (And.intro hc hd))
  · rintro ⟨ha, hb, hc, hd⟩
    apply List.mem_map.mpr
    refine ⟨((r 0, r 1), (r 2, r 3)), ?_, four_eta r⟩
    exact (mem_listProduct _ _ _ _).2 ⟨(mem_listProduct _ _ _ _).2 ⟨ha, hb⟩,
      (mem_listProduct _ _ _ _).2 ⟨hc, hd⟩⟩

theorem listFour_nodup (xs ys zs ws : List α)
    (hx : xs.Nodup) (hy : ys.Nodup) (hz : zs.Nodup) (hw : ws.Nodup) :
    (listFour xs ys zs ws).Nodup := by
  apply nodup_map_injective _ _ (listProduct_nodup _ _
    (listProduct_nodup _ _ hx hy) (listProduct_nodup _ _ hz hw))
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ he
  have h0 := congrFun he (0 : Fin 4)
  have h1 := congrFun he (1 : Fin 4)
  have h2 := congrFun he (2 : Fin 4)
  have h3 := congrFun he (3 : Fin 4)
  exact Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3)

def blockPositions (h : Nat) (b : Block) (hb : ValidBlock h b) : List (PhysicalPosition h) :=
  (List.finRange (blockSize h b)).map (fun k => ⟨b, hb, k.val, k.isLt⟩)

theorem blockPositions_length (h : Nat) (b : Block) (hb : ValidBlock h b) :
    (blockPositions h b hb).length = blockSize h b := by simp [blockPositions]

theorem mem_blockPositions (h : Nat) (b : Block) (hb : ValidBlock h b) (x : PhysicalPosition h) :
    x ∈ blockPositions h b hb ↔ x.block = b := by
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
    rfl
  · intro he
    let k : Fin (blockSize h b) := ⟨x.offset, by rw [← he]; exact x.offset_lt⟩
    apply List.mem_map.mpr
    refine ⟨k, finRange_mem _ _, ?_⟩
    exact physicalPosition_ext _ _ he.symm rfl

theorem blockPositions_nodup (h : Nat) (b : Block) (hb : ValidBlock h b) :
    (blockPositions h b hb).Nodup := by
  apply nodup_map_injective _ _ (finRange_nodup _)
  intro i j he
  exact Fin.ext (congrArg PhysicalPosition.offset he)

def tuplePositions (h : Nat) (r : Fin 4 → Block) (hr : ∀ i, ValidBlock h (r i)) :
    List (Fin 4 → PhysicalPosition h) :=
  listFour (blockPositions h (r 0) (hr 0)) (blockPositions h (r 1) (hr 1))
    (blockPositions h (r 2) (hr 2)) (blockPositions h (r 3) (hr 3))

theorem tuplePositions_length (h : Nat) (r : Fin 4 → Block) (hr : ∀ i, ValidBlock h (r i)) :
    (tuplePositions h r hr).length = tupleWeight h r := by
  simp [tuplePositions, listFour_length, blockPositions_length, tupleWeight]

theorem mem_tuplePositions (h : Nat) (r : Fin 4 → Block) (hr : ∀ i, ValidBlock h (r i))
    (x : Fin 4 → PhysicalPosition h) :
    x ∈ tuplePositions h r hr ↔ (fun i => (x i).block) = r := by
  simp only [tuplePositions, mem_listFour, mem_blockPositions]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    rw [← four_eta (fun i => (x i).block), ← four_eta r, h0, h1, h2, h3]
  · intro he
    exact ⟨congrFun he 0, congrFun he 1, congrFun he 2, congrFun he 3⟩

theorem tuplePositions_nodup (h : Nat) (r : Fin 4 → Block) (hr : ∀ i, ValidBlock h (r i)) :
    (tuplePositions h r hr).Nodup :=
  listFour_nodup _ _ _ _ (blockPositions_nodup ..) (blockPositions_nodup ..)
    (blockPositions_nodup ..) (blockPositions_nodup ..)

def copyFibre (h : Nat) (repair : Bool) (r c : Fin 4 → Block)
    (hc : ValidCopy h (quotientHost h repair) r c) :
    List ((Fin 4 → PhysicalPosition h) × (Fin 4 → PhysicalPosition h)) :=
  listProduct (tuplePositions h r hc.1) (tuplePositions h c hc.2.1)

theorem copyFibre_length (h : Nat) (repair : Bool) (r c : Fin 4 → Block)
    (hc : ValidCopy h (quotientHost h repair) r c) :
    (copyFibre h repair r c hc).length = copyWeight h r c := by
  simp [copyFibre, listProduct_length, tuplePositions_length, copyWeight]

theorem copyFibre_nodup (h : Nat) (repair : Bool) (r c : Fin 4 → Block)
    (hc : ValidCopy h (quotientHost h repair) r c) :
    (copyFibre h repair r c hc).Nodup :=
  listProduct_nodup _ _ (tuplePositions_nodup ..) (tuplePositions_nodup ..)

theorem mem_copyFibre (h : Nat) (repair : Bool) (r c : Fin 4 → Block)
    (hc : ValidCopy h (quotientHost h repair) r c)
    (x y : Fin 4 → PhysicalPosition h) :
    (x, y) ∈ copyFibre h repair r c hc ↔
      (fun i => (x i).block) = r ∧ (fun i => (y i).block) = c := by
  simp [copyFibre, mem_listProduct, mem_tuplePositions]

theorem copyFibre_sound (h : Nat) (repair : Bool) (r c : Fin 4 → Block)
    (hc : ValidCopy h (quotientHost h repair) r c)
    (x y : Fin 4 → PhysicalPosition h) (hm : (x, y) ∈ copyFibre h repair r c hc) :
    MatrixCopy (physicalHost h repair) x y := by
  rcases (mem_copyFibre _ _ _ _ _ _ _).1 hm with ⟨hr, hcols⟩
  apply valid_copy_arbitrary_offsets
  simpa only [hr, hcols] using hc

def terminalIPhysical (h : Nat) (hh : 1 ≤ h) :
    List ((Fin 4 → PhysicalPosition h) × (Fin 4 → PhysicalPosition h)) :=
  (List.finRange (2 ^ h)).flatMap (fun p =>
    copyFibre h false (terminalRows h p.val) (terminalIColumns h p.val)
      (by simpa only [quotientHost] using terminalI_validCopy h p.val hh p.isLt))

def terminalIIPhysical (h : Nat) (hh : 1 ≤ h) :
    List ((Fin 4 → PhysicalPosition h) × (Fin 4 → PhysicalPosition h)) :=
  (sameParityPairs (2 ^ h)).attach.flatMap (fun pq =>
    copyFibre h false (terminalRows h pq.val.1) (terminalIIColumns h pq.val.1 pq.val.2)
      (by simpa only [quotientHost] using (terminalII_validCopy h pq.val.1 pq.val.2 hh
        ((mem_sameParityPairs ..).1 pq.property).1
        ((mem_sameParityPairs ..).1 pq.property).2.1
        ((mem_sameParityPairs ..).1 pq.property).2.2)))

def terminalPhysicalCopies (h : Nat) (hh : 1 ≤ h) :=
  terminalIPhysical h hh ++ terminalIIPhysical h hh

theorem terminalIPhysical_length (h : Nat) (hh : 1 ≤ h) :
    (terminalIPhysical h hh).length = 2 * (2 ^ h) ^ 6 := by
  rw [terminalIPhysical, List.length_flatMap]
  simp only [copyFibre_length, copyWeight, tupleWeight]
  have hw : ((List.finRange (2 ^ h)).map (fun p =>
      copyWeight h (terminalRows h p.val) (terminalIColumns h p.val))) =
      List.replicate (List.finRange (2 ^ h)).length (2 * (2 ^ h) ^ 5) := by
    apply List.map_eq_replicate_iff.mpr
    intro p _
    exact terminalI_weight h p.val hh
  change ((List.finRange (2 ^ h)).map (fun p =>
    copyWeight h (terminalRows h p.val) (terminalIColumns h p.val))).sum = _
  rw [hw]
  simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

theorem terminalIIPhysical_length (h : Nat) (hh : 1 ≤ h) :
    (terminalIIPhysical h hh).length = ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 := by
  rw [terminalIIPhysical, List.length_flatMap]
  simp only [copyFibre_length]
  have hw : ((sameParityPairs (2 ^ h)).attach.map (fun pq =>
      copyWeight h (terminalRows h pq.val.1) (terminalIIColumns h pq.val.1 pq.val.2))) =
      List.replicate (sameParityPairs (2 ^ h)).attach.length (2 * (2 ^ h) ^ 4) := by
    apply List.map_eq_replicate_iff.mpr
    intro pq _
    exact terminalII_weight h pq.val.1 pq.val.2 hh
  rw [hw]
  simp only [List.sum_replicate_nat, List.length_attach, sameParityPairs_length_power h hh]
  have hm : 2 ^ h = 2 * 2 ^ (h - 1) := by
    rw [Nat.mul_comm]; exact (Nat.two_pow_pred_mul_two hh).symm
  have hd : (2 ^ h - 2) / 2 = 2 ^ (h - 1) - 1 := by rw [hm]; omega
  rw [hd]
  simp [Nat.pow_succ, hm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem terminalPhysicalCopies_length (h : Nat) (hh : 1 ≤ h) :
    (terminalPhysicalCopies h hh).length =
      2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 := by
  simp [terminalPhysicalCopies, terminalIPhysical_length, terminalIIPhysical_length]

theorem terminalIPhysical_nodup (h : Nat) (hh : 1 ≤ h) : (terminalIPhysical h hh).Nodup := by
  apply nodup_flatMap_disjoint _ _ (finRange_nodup _)
  · intro p _
    exact copyFibre_nodup ..
  · intro p _ q _ hne x hx y hy he
    have hp := (mem_copyFibre ..).1 hx
    have hq := (mem_copyFibre ..).1 hy
    have hblocks := hp.1.symm.trans (by simpa only [he] using hq.1)
    exact hne (Fin.ext (terminalRows_parameter_injective _ _ _ hblocks))

theorem terminalIIPhysical_nodup (h : Nat) (hh : 1 ≤ h) : (terminalIIPhysical h hh).Nodup := by
  have ha : (sameParityPairs (2 ^ h)).attach.Nodup := by
    apply List.Pairwise.of_map (S := fun a b : Nat × Nat => a ≠ b) Subtype.val
      (fun a b hab he => hab (congrArg Subtype.val he))
    simpa only [List.attach_map_subtype_val] using sameParityPairs_nodup (2 ^ h)
  apply nodup_flatMap_disjoint _ _ ha
  · intro pq _
    exact copyFibre_nodup ..
  · intro pq _ uv _ hne x hx y hy he
    have hp := (mem_copyFibre ..).1 hx
    have hq := (mem_copyFibre ..).1 hy
    have hrows := hp.1.symm.trans (by simpa only [he] using hq.1)
    have hcols := hp.2.symm.trans (by simpa only [he] using hq.2)
    have hpq := terminalRows_parameter_injective _ _ _ hrows
    have hpuv : pq.val.2 = uv.val.2 := by
      rw [hpq] at hcols
      exact terminalII_parameter_injective _ _ _ _ hcols
    exact hne (Subtype.ext (Prod.ext hpq hpuv))

theorem terminalPhysicalCopies_nodup (h : Nat) (hh : 1 ≤ h) :
    (terminalPhysicalCopies h hh).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨terminalIPhysical_nodup h hh, terminalIIPhysical_nodup h hh, ?_⟩
  intro x hx y hy he
  rcases List.mem_flatMap.mp hx with ⟨p, _, hx⟩
  rcases List.mem_flatMap.mp hy with ⟨pq, _, hy⟩
  have hp := (mem_copyFibre ..).1 hx
  have hq := (mem_copyFibre ..).1 hy
  exact terminalForms_disjoint h p.val pq.val.1 pq.val.2
    (hp.2.symm.trans (by simpa only [he] using hq.2))

theorem terminalPhysicalCopies_sound (h : Nat) (hh : 1 ≤ h)
    (r c : Fin 4 → PhysicalPosition h) (hm : (r, c) ∈ terminalPhysicalCopies h hh) :
    MatrixCopy (physicalHost h) r c := by
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_flatMap.mp hm with ⟨p, _, hm⟩
    exact copyFibre_sound _ _ _ _ _ _ _ hm
  · rcases List.mem_flatMap.mp hm with ⟨pq, _, hm⟩
    exact copyFibre_sound _ _ _ _ _ _ _ hm

end H4Formal
