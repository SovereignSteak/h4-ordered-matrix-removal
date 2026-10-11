import H4Formal.PhysicalOrder
import H4Formal.CanonicalEdits

namespace H4Formal

def hostSize (h : Nat) := (14 * h + 2) * 2 ^ h

def allPhysicalPositions (h : Nat) : List (PhysicalPosition h) :=
  (List.finRange (hostSize h)).map (indexedPosition h)

theorem allPhysicalPositions_length (h : Nat) : (allPhysicalPositions h).length = hostSize h := by
  simp [allPhysicalPositions]

theorem allPhysicalPositions_nodup (h : Nat) : (allPhysicalPositions h).Nodup := by
  apply nodup_map_injective _ _ (finRange_nodup _)
  exact indexedPosition_injective h

theorem mem_allPhysicalPositions (h : Nat) (x : PhysicalPosition h) :
    x ∈ allPhysicalPositions h := by
  obtain ⟨i, hi⟩ := indexedPosition_surjective h x
  exact List.mem_map.mpr ⟨i, finRange_mem _ i, hi⟩

def physicalLE {h : Nat} (axis : Axis) (x y : PhysicalPosition h) : Prop :=
  physicalBefore axis x y ∨ x = y

instance {h : Nat} (axis : Axis) (x y : PhysicalPosition h) :
    Decidable (physicalBefore axis x y) := by
  unfold physicalBefore
  infer_instance

noncomputable instance {h : Nat} (axis : Axis) (x y : PhysicalPosition h) : Decidable (physicalLE axis x y) := by
  classical
  unfold physicalLE
  infer_instance

theorem physicalLE_trans (axis : Axis) (h : Nat) (x y z : PhysicalPosition h)
    (hxy : physicalLE axis x y) (hyz : physicalLE axis y z) : physicalLE axis x z := by
  rcases hxy with hxy | rfl <;> rcases hyz with hyz | rfl
  · exact Or.inl (physicalBefore_trans axis h x y z hxy hyz)
  · exact Or.inl hxy
  · exact Or.inl hyz
  · exact Or.inr rfl

noncomputable def orderedPositions (axis : Axis) (h : Nat) : List (PhysicalPosition h) :=
  (allPhysicalPositions h).mergeSort (fun x y => decide (physicalLE axis x y))

theorem orderedPositions_length (axis : Axis) (h : Nat) :
    (orderedPositions axis h).length = hostSize h := by
  simp [orderedPositions, allPhysicalPositions_length]

theorem orderedPositions_nodup (axis : Axis) (h : Nat) : (orderedPositions axis h).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (allPhysicalPositions_nodup h)

theorem mem_orderedPositions (axis : Axis) (h : Nat) (x : PhysicalPosition h) :
    x ∈ orderedPositions axis h := by
  simpa only [orderedPositions, List.mem_mergeSort] using mem_allPhysicalPositions h x

theorem orderedPositions_sorted (axis : Axis) (h : Nat) :
    (orderedPositions axis h).Pairwise (physicalLE axis) := by
  have hs : (orderedPositions axis h).Pairwise (fun x y => decide (physicalLE axis x y) = true) := by
    apply List.sorted_mergeSort
    · intro x y z hxy hyz
      simp only [decide_eq_true_eq] at hxy hyz ⊢
      exact physicalLE_trans axis h x y z hxy hyz
    · intro x y
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rcases physicalBefore_total axis h x y with hxy | rfl | hyx
      · exact Or.inl (Or.inl hxy)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (Or.inl hyx)
  simpa only [decide_eq_true_eq] using hs

noncomputable def orderedPosition (axis : Axis) (h : Nat) (i : Fin (hostSize h)) :
    PhysicalPosition h :=
  (orderedPositions axis h)[i.val]'(by rw [orderedPositions_length]; exact i.isLt)

theorem orderedPosition_injective (axis : Axis) (h : Nat)
    (i j : Fin (hostSize h)) (he : orderedPosition axis h i = orderedPosition axis h j) : i = j := by
  apply Fin.ext
  have hi : i.val < (orderedPositions axis h).length := by rw [orderedPositions_length]; exact i.isLt
  have hj : j.val < (orderedPositions axis h).length := by rw [orderedPositions_length]; exact j.isLt
  apply List.getElem?_inj hi (orderedPositions_nodup axis h)
  simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, orderedPosition]
    using congrArg some he

theorem orderedPosition_surjective (axis : Axis) (h : Nat) (x : PhysicalPosition h) :
    ∃ i : Fin (hostSize h), orderedPosition axis h i = x := by
  rcases List.mem_iff_getElem.mp (mem_orderedPositions axis h x) with ⟨i, hi, he⟩
  exact ⟨⟨i, by rw [← orderedPositions_length axis h]; exact hi⟩, he⟩

theorem orderedPosition_increasing (axis : Axis) (h : Nat) (i j : Fin (hostSize h))
    (hij : i.val < j.val) : physicalBefore axis (orderedPosition axis h i) (orderedPosition axis h j) := by
  have hi : i.val < (orderedPositions axis h).length := by rw [orderedPositions_length]; exact i.isLt
  have hj : j.val < (orderedPositions axis h).length := by rw [orderedPositions_length]; exact j.isLt
  have hs := (List.pairwise_iff_getElem.mp (orderedPositions_sorted axis h)) i.val j.val hi hj hij
  rcases hs with hs | he
  · exact hs
  · have hij' := orderedPosition_injective axis h i j he
    cases hij'
    omega

theorem orderedPosition_order_iff (axis : Axis) (h : Nat) (i j : Fin (hostSize h)) :
    physicalBefore axis (orderedPosition axis h i) (orderedPosition axis h j) ↔ i.val < j.val := by
  constructor
  · intro ho
    by_cases he : i = j
    · subst j
      exact False.elim (physicalBefore_irrefl axis h _ ho)
    · have hn : i.val ≠ j.val := fun hh => he (Fin.ext hh)
      rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
      · exact hlt
      · have hr := orderedPosition_increasing axis h j i hgt
        exact False.elim (physicalBefore_irrefl axis h _ (physicalBefore_trans axis h _ _ _ ho hr))
  · exact orderedPosition_increasing axis h i j

noncomputable def orderedIndex (axis : Axis) (h : Nat) (x : PhysicalPosition h) : Fin (hostSize h) :=
  Classical.choose (orderedPosition_surjective axis h x)

theorem orderedPosition_orderedIndex (axis : Axis) (h : Nat) (x : PhysicalPosition h) :
    orderedPosition axis h (orderedIndex axis h x) = x :=
  Classical.choose_spec (orderedPosition_surjective axis h x)

theorem orderedIndex_orderedPosition (axis : Axis) (h : Nat) (i : Fin (hostSize h)) :
    orderedIndex axis h (orderedPosition axis h i) = i := by
  apply orderedPosition_injective axis h
  exact orderedPosition_orderedIndex axis h _

/-- The ordinary square matrix: both axes use numeric strict order. -/
noncomputable def standardHost (h : Nat) (repair : Bool := false) :
    OrderedMatrix (Fin (hostSize h)) (Fin (hostSize h)) where
  value i j := (physicalHost h repair).value (orderedPosition .row h i) (orderedPosition .column h j)
  rowBefore i j := i.val < j.val
  colBefore i j := i.val < j.val

theorem standard_copy_iff (h : Nat) (repair : Bool) (r c : Fin 4 → Fin (hostSize h)) :
    MatrixCopy (standardHost h repair) r c ↔
      MatrixCopy (physicalHost h repair) (fun i => orderedPosition .row h (r i))
        (fun i => orderedPosition .column h (c i)) := by
  constructor
  · intro hc
    exact ⟨fun i j hij => (orderedPosition_order_iff .row h _ _).2 (hc.1 i j hij),
      fun i j hij => (orderedPosition_order_iff .column h _ _).2 (hc.2.1 i j hij), hc.2.2⟩
  · intro hc
    exact ⟨fun i j hij => (orderedPosition_order_iff .row h _ _).1 (hc.1 i j hij),
      fun i j hij => (orderedPosition_order_iff .column h _ _).1 (hc.2.1 i j hij), hc.2.2⟩

theorem standard_free_iff (h : Nat) (repair : Bool) :
    PatternFree (standardHost h repair) ↔ PatternFree (physicalHost h repair) := by
  constructor
  · intro hf r c hc
    apply hf (fun i => orderedIndex .row h (r i)) (fun i => orderedIndex .column h (c i))
    apply (standard_copy_iff h repair _ _).2
    simpa only [orderedPosition_orderedIndex] using hc
  · intro hf r c hc
    exact hf _ _ ((standard_copy_iff h repair r c).1 hc)

end H4Formal
