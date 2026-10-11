import H4Formal.GlobalCounting
import H4Formal.EditLowerBound

namespace H4Formal

def withValues {n : Nat} (A : OrderedMatrix (Fin n) (Fin n))
    (D : Fin n → Fin n → Bool) : OrderedMatrix (Fin n) (Fin n) where
  value := D
  rowBefore := A.rowBefore
  colBefore := A.colBefore

noncomputable def changedCells {n : Nat} (A : OrderedMatrix (Fin n) (Fin n))
    (D : Fin n → Fin n → Bool) : List (Fin n × Fin n) := by
  classical
  exact (listProduct (List.finRange n) (List.finRange n)).filter
    (fun x => decide (D x.1 x.2 ≠ A.value x.1 x.2))

theorem mem_changedCells {n : Nat} (A : OrderedMatrix (Fin n) (Fin n))
    (D : Fin n → Fin n → Bool) (i j : Fin n) :
    (i, j) ∈ changedCells A D ↔ D i j ≠ A.value i j := by
  classical
  simp [changedCells, mem_listProduct, finRange_mem]

theorem changedCells_nodup {n : Nat} (A : OrderedMatrix (Fin n) (Fin n))
    (D : Fin n → Fin n → Bool) : (changedCells A D).Nodup := by
  classical
  exact (listProduct_nodup _ _ (finRange_nodup _) (finRange_nodup _)).filter _

noncomputable def editCost {n : Nat} (A : OrderedMatrix (Fin n) (Fin n))
    (D : Fin n → Fin n → Bool) : Nat := (changedCells A D).length

theorem least_nat_of_exists {P : Nat → Prop} (hp : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  classical
  have aux : ∀ N, (∃ k, k ≤ N ∧ P k) → ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
    intro N
    induction N with
    | zero =>
      rintro ⟨k, hk, hp⟩
      have he : k = 0 := by omega
      subst k
      exact ⟨0, hp, fun _ _ => Nat.zero_le _⟩
    | succ N ih =>
      intro hex
      by_cases hsmall : ∃ k, k ≤ N ∧ P k
      · exact ih hsmall
      · obtain ⟨k, hk, hp⟩ := hex
        have he : k = N + 1 := by
          apply Classical.byContradiction
          intro hn
          exact hsmall ⟨k, by omega, hp⟩
        subst k
        refine ⟨N + 1, hp, ?_⟩
        intro j hj
        apply Classical.byContradiction
        intro hn
        exact hsmall ⟨j, by omega, hj⟩
  obtain ⟨k, hk⟩ := hp
  exact aux k ⟨k, Nat.le_refl _, hk⟩

theorem free_repair_exists {n : Nat} (A : OrderedMatrix (Fin n) (Fin n)) :
    ∃ D, PatternFree (withValues A D) := by
  refine ⟨fun _ _ => true, ?_⟩
  intro r c hc
  have hz := hc.2.2 0 0
  simp [withValues, pattern] at hz

theorem least_repair_cost_exists {n : Nat} (A : OrderedMatrix (Fin n) (Fin n)) :
    ∃ k, (∃ D, PatternFree (withValues A D) ∧ editCost A D = k) ∧
      ∀ j, (∃ D, PatternFree (withValues A D) ∧ editCost A D = j) → k ≤ j := by
  obtain ⟨D, hf⟩ := free_repair_exists A
  exact least_nat_of_exists ⟨editCost A D, D, hf, rfl⟩

/-- Minimum Hamming distance over every pattern-free Boolean repair. -/
noncomputable def editDistance {n : Nat} (A : OrderedMatrix (Fin n) (Fin n)) : Nat :=
  Classical.choose (least_repair_cost_exists A)

theorem editDistance_attained {n : Nat} (A : OrderedMatrix (Fin n) (Fin n)) :
    ∃ D, PatternFree (withValues A D) ∧ editCost A D = editDistance A :=
  (Classical.choose_spec (least_repair_cost_exists A)).1

theorem editDistance_le_cost {n : Nat} (A : OrderedMatrix (Fin n) (Fin n))
    (D : Fin n → Fin n → Bool) (hf : PatternFree (withValues A D)) :
    editDistance A ≤ editCost A D :=
  (Classical.choose_spec (least_repair_cost_exists A)).2 _ ⟨D, hf, rfl⟩

noncomputable def toPhysicalCell (h : Nat) (x : Fin (hostSize h) × Fin (hostSize h)) :=
  (orderedPosition .row h x.1, orderedPosition .column h x.2)

noncomputable def toStandardCell (h : Nat) (x : PhysicalPosition h × PhysicalPosition h) :=
  (orderedIndex .row h x.1, orderedIndex .column h x.2)

theorem toPhysicalCell_toStandardCell (h : Nat) (x) :
    toPhysicalCell h (toStandardCell h x) = x := by
  apply Prod.ext <;> exact orderedPosition_orderedIndex _ _ _

theorem toStandardCell_toPhysicalCell (h : Nat) (x) :
    toStandardCell h (toPhysicalCell h x) = x := by
  apply Prod.ext <;> exact orderedIndex_orderedPosition _ _ _

theorem toStandardCell_injective (h : Nat) (x y)
    (he : toStandardCell h x = toStandardCell h y) : x = y := by
  have hh := congrArg (toPhysicalCell h) he
  simpa only [toPhysicalCell_toStandardCell] using hh

theorem edited_standard_free_lifts (h : Nat)
    (D : Fin (hostSize h) → Fin (hostSize h) → Bool)
    (hf : PatternFree (withValues (standardHost h) D)) :
    PatternFree (editedHost h (fun r c => D (orderedIndex .row h r) (orderedIndex .column h c))) := by
  intro r c hc
  apply hf (fun i => orderedIndex .row h (r i)) (fun i => orderedIndex .column h (c i))
  refine ⟨?_, ?_, hc.2.2⟩
  · intro i j hij
    apply (orderedPosition_order_iff .row h _ _).1
    simpa only [orderedPosition_orderedIndex] using hc.1 i j hij
  · intro i j hij
    apply (orderedPosition_order_iff .column h _ _).1
    simpa only [orderedPosition_orderedIndex] using hc.2.1 i j hij

theorem standard_edit_lower_bound (h : Nat) (hh : 1 ≤ h)
    (D : Fin (hostSize h) → Fin (hostSize h) → Bool)
    (hf : PatternFree (withValues (standardHost h) D)) :
    2 ^ h * 2 ^ h ≤ editCost (standardHost h) D := by
  let Dp := fun r c => D (orderedIndex .row h r) (orderedIndex .column h c)
  have covers : ∀ r c, Dp r c ≠ hostValue h r.block c.block →
      (r, c) ∈ (changedCells (standardHost h) D).map (toPhysicalCell h) := by
    intro r c he
    refine List.mem_map.mpr ⟨(orderedIndex .row h r, orderedIndex .column h c), ?_, ?_⟩
    · apply (mem_changedCells ..).2
      simpa only [standardHost, physicalHost, Bool.false_eq_true, if_false,
        orderedPosition_orderedIndex] using he
    · exact toPhysicalCell_toStandardCell h (r, c)
  have hl := arbitrary_edit_lower_bound h hh Dp _ covers (edited_standard_free_lifts h D hf)
  simpa only [List.length_map, editCost] using hl

theorem standard_distance_lower_bound (h : Nat) (hh : 1 ≤ h) :
    2 ^ h * 2 ^ h ≤ editDistance (standardHost h) := by
  obtain ⟨D, hf, he⟩ := editDistance_attained (standardHost h)
  rw [← he]
  exact standard_edit_lower_bound h hh D hf

theorem mem_mapped_canonicalEdits (h : Nat) (x : Fin (hostSize h) × Fin (hostSize h)) :
    x ∈ (canonicalEdits h).map (toStandardCell h) ↔
      x ∈ changedCells (standardHost h) (standardHost h true).value := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    apply (mem_changedCells ..).2
    have he := (canonicalEdits_exact h y.1 y.2).1 hy
    simpa only [toStandardCell, standardHost, physicalHost, Bool.false_eq_true, if_false, if_true,
      orderedPosition_orderedIndex] using he
  · intro hx
    have he := (mem_changedCells ..).1 hx
    refine List.mem_map.mpr ⟨toPhysicalCell h x, ?_, toStandardCell_toPhysicalCell h x⟩
    apply (canonicalEdits_exact ..).2
    simpa only [toPhysicalCell, standardHost, physicalHost, Bool.false_eq_true, if_false, if_true] using he

theorem canonical_editCost (h : Nat) :
    editCost (standardHost h) (standardHost h true).value = 2 ^ h * 2 ^ h := by
  unfold editCost
  rw [← canonicalEdits_length h, ← List.length_map (toStandardCell h)]
  apply nodup_same_members_length _ _ (changedCells_nodup _ _)
    (nodup_map_injective _ _ (canonicalEdits_nodup h) (toStandardCell_injective h))
  intro x
  exact (mem_mapped_canonicalEdits h x).symm

theorem standard_distance_of_free_repair (h : Nat) (hh : 1 ≤ h)
    (hf : PatternFree (standardHost h true)) :
    editDistance (standardHost h) = 2 ^ h * 2 ^ h := by
  apply Nat.le_antisymm
  · rw [← canonical_editCost h]
    apply editDistance_le_cost
    exact hf
  · exact standard_distance_lower_bound h hh

end H4Formal
