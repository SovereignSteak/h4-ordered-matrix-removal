import H4Formal.StandardMatrix
import H4Formal.TerminalDecode

namespace H4Formal

def TerminalExhaustion (h : Nat) : Prop :=
  ∀ r c, ValidCopy h (originalHost h) r c →
    ∃ p, p < 2 ^ h ∧ r = terminalRows h p ∧
      (c = terminalIColumns h p ∨
        ∃ q, q < p ∧ q % 2 = p % 2 ∧ c = terminalIIColumns h p q)

theorem terminalPhysicalCopies_complete (h : Nat) (hh : 1 ≤ h) (hex : TerminalExhaustion h)
    (r c : Fin 4 → PhysicalPosition h) (hc : MatrixCopy (physicalHost h) r c) :
    (r, c) ∈ terminalPhysicalCopies h hh := by
  have hq := physical_copy_projects h false r c hc
  have hq' : ValidCopy h (originalHost h) (fun i => (r i).block) (fun i => (c i).block) := by
    simpa only [quotientHost] using hq
  obtain ⟨p, hp, hr, hcols⟩ := hex _ _ hq'
  apply List.mem_append.mpr
  rcases hcols with hI | ⟨q, hqp, hpar, hII⟩
  · left
    apply List.mem_flatMap.mpr
    refine ⟨⟨p, hp⟩, finRange_mem _ _, ?_⟩
    exact (mem_copyFibre _ _ _ _ _ _ _).2 ⟨hr, hI⟩
  · right
    have hpq : (p, q) ∈ sameParityPairs (2 ^ h) := (mem_sameParityPairs ..).2 ⟨hp, hqp, hpar⟩
    apply List.mem_flatMap.mpr
    refine ⟨⟨(p, q), hpq⟩, List.mem_attach _ _, ?_⟩
    exact (mem_copyFibre _ _ _ _ _ _ _).2 ⟨hr, hII⟩

theorem nodup_same_members_length {α : Type u} (xs ys : List α)
    (hx : xs.Nodup) (hy : ys.Nodup) (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.length = ys.length := by
  classical
  have hp : xs.Perm ys := List.perm_iff_count.mpr (fun x => by
    simp only [hx.count, hy.count, hm x])
  exact hp.length_eq

noncomputable instance (h : Nat) (repair : Bool) (r c : Fin 4 → PhysicalPosition h) :
    Decidable (MatrixCopy (physicalHost h repair) r c) := by
  classical
  unfold MatrixCopy
  infer_instance

noncomputable instance (h : Nat) (repair : Bool) (r c : Fin 4 → Fin (hostSize h)) :
    Decidable (MatrixCopy (standardHost h repair) r c) := by
  classical
  unfold MatrixCopy
  infer_instance

def allPhysicalFour (h : Nat) := listFour (allPhysicalPositions h) (allPhysicalPositions h)
  (allPhysicalPositions h) (allPhysicalPositions h)

theorem mem_allPhysicalFour (h : Nat) (r : Fin 4 → PhysicalPosition h) : r ∈ allPhysicalFour h :=
  (mem_listFour ..).2 ⟨mem_allPhysicalPositions h _, mem_allPhysicalPositions h _,
    mem_allPhysicalPositions h _, mem_allPhysicalPositions h _⟩

theorem allPhysicalFour_nodup (h : Nat) : (allPhysicalFour h).Nodup :=
  listFour_nodup _ _ _ _ (allPhysicalPositions_nodup h) (allPhysicalPositions_nodup h)
    (allPhysicalPositions_nodup h) (allPhysicalPositions_nodup h)

noncomputable def physicalCopyEnumeration (h : Nat) (repair : Bool := false) :=
  (listProduct (allPhysicalFour h) (allPhysicalFour h)).filter
    (fun x => decide (MatrixCopy (physicalHost h repair) x.1 x.2))

theorem mem_physicalCopyEnumeration (h : Nat) (repair : Bool) (r c : Fin 4 → PhysicalPosition h) :
    (r, c) ∈ physicalCopyEnumeration h repair ↔ MatrixCopy (physicalHost h repair) r c := by
  simp [physicalCopyEnumeration, mem_listProduct, mem_allPhysicalFour]

theorem physicalCopyEnumeration_nodup (h : Nat) (repair : Bool) :
    (physicalCopyEnumeration h repair).Nodup :=
  (listProduct_nodup _ _ (allPhysicalFour_nodup h) (allPhysicalFour_nodup h)).filter _

theorem physicalCopyEnumeration_length_of_exhaustion (h : Nat) (hh : 1 ≤ h)
    (hex : TerminalExhaustion h) :
    (physicalCopyEnumeration h).length =
      2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 := by
  rw [← terminalPhysicalCopies_length h hh]
  apply nodup_same_members_length _ _ (physicalCopyEnumeration_nodup h false)
    (terminalPhysicalCopies_nodup h hh)
  rintro ⟨r, c⟩
  rw [mem_physicalCopyEnumeration]
  exact ⟨terminalPhysicalCopies_complete h hh hex r c, terminalPhysicalCopies_sound h hh r c⟩

def allStandardFour (h : Nat) := listFour (List.finRange (hostSize h)) (List.finRange (hostSize h))
  (List.finRange (hostSize h)) (List.finRange (hostSize h))

theorem mem_allStandardFour (h : Nat) (r : Fin 4 → Fin (hostSize h)) : r ∈ allStandardFour h :=
  (mem_listFour ..).2 ⟨finRange_mem _ _, finRange_mem _ _, finRange_mem _ _, finRange_mem _ _⟩

theorem allStandardFour_nodup (h : Nat) : (allStandardFour h).Nodup :=
  listFour_nodup _ _ _ _ (finRange_nodup _) (finRange_nodup _) (finRange_nodup _) (finRange_nodup _)

noncomputable def standardCopyEnumeration (h : Nat) (repair : Bool := false) :=
  (listProduct (allStandardFour h) (allStandardFour h)).filter
    (fun x => decide (MatrixCopy (standardHost h repair) x.1 x.2))

theorem mem_standardCopyEnumeration (h : Nat) (repair : Bool) (r c : Fin 4 → Fin (hostSize h)) :
    (r, c) ∈ standardCopyEnumeration h repair ↔ MatrixCopy (standardHost h repair) r c := by
  simp [standardCopyEnumeration, mem_listProduct, mem_allStandardFour]

theorem standardCopyEnumeration_nodup (h : Nat) (repair : Bool) :
    (standardCopyEnumeration h repair).Nodup :=
  (listProduct_nodup _ _ (allStandardFour_nodup h) (allStandardFour_nodup h)).filter _

noncomputable def standardEmbedding (h : Nat)
    (x : (Fin 4 → PhysicalPosition h) × (Fin 4 → PhysicalPosition h)) :=
  ((fun i => orderedIndex .row h (x.1 i)), (fun i => orderedIndex .column h (x.2 i)))

noncomputable def physicalEmbedding (h : Nat)
    (x : (Fin 4 → Fin (hostSize h)) × (Fin 4 → Fin (hostSize h))) :=
  ((fun i => orderedPosition .row h (x.1 i)), (fun i => orderedPosition .column h (x.2 i)))

theorem physicalEmbedding_standardEmbedding (h : Nat) (x) :
    physicalEmbedding h (standardEmbedding h x) = x := by
  apply Prod.ext <;> funext i <;> exact orderedPosition_orderedIndex _ h _

theorem standardEmbedding_physicalEmbedding (h : Nat) (x) :
    standardEmbedding h (physicalEmbedding h x) = x := by
  apply Prod.ext <;> funext i <;> exact orderedIndex_orderedPosition _ h _

theorem standardEmbedding_injective (h : Nat) (x y) (he : standardEmbedding h x = standardEmbedding h y) :
    x = y := by
  have hh := congrArg (physicalEmbedding h) he
  simpa only [physicalEmbedding_standardEmbedding] using hh

theorem mem_mapped_physicalCopyEnumeration (h : Nat) (repair : Bool)
    (x : (Fin 4 → Fin (hostSize h)) × (Fin 4 → Fin (hostSize h))) :
    x ∈ (physicalCopyEnumeration h repair).map (standardEmbedding h) ↔
      MatrixCopy (standardHost h repair) x.1 x.2 := by
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hc := (mem_physicalCopyEnumeration h repair y.1 y.2).1 hy
    apply (standard_copy_iff h repair _ _).2
    simpa only [standardEmbedding, orderedPosition_orderedIndex] using hc
  · intro hc
    have hp := (standard_copy_iff h repair x.1 x.2).1 hc
    refine List.mem_map.mpr ⟨physicalEmbedding h x, ?_, standardEmbedding_physicalEmbedding h x⟩
    exact (mem_physicalCopyEnumeration _ _ _ _).2 hp

theorem standardCopyEnumeration_length (h : Nat) (repair : Bool) :
    (standardCopyEnumeration h repair).length = (physicalCopyEnumeration h repair).length := by
  rw [← List.length_map (standardEmbedding h)]
  apply nodup_same_members_length _ _ (standardCopyEnumeration_nodup h repair)
    (nodup_map_injective _ _ (physicalCopyEnumeration_nodup h repair) (standardEmbedding_injective h))
  rintro ⟨r, c⟩
  rw [mem_standardCopyEnumeration, mem_mapped_physicalCopyEnumeration]

noncomputable def hostCopyCount (h : Nat) := (standardCopyEnumeration h).length

theorem hostCopyCount_of_exhaustion (h : Nat) (hh : 1 ≤ h) (hex : TerminalExhaustion h) :
    hostCopyCount h = 2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 := by
  unfold hostCopyCount
  rw [standardCopyEnumeration_length]
  exact physicalCopyEnumeration_length_of_exhaustion h hh hex

end H4Formal
