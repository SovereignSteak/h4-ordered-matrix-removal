import H4Formal.IndexedMatrixCore

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

abbrev MarkerPermutation (h : Nat) := Equiv.Perm (Fin h × Fin 6)

def relabelMarkers (h : Nat) (perm : MarkerPermutation h) : PhysicalPosition h ≃ PhysicalPosition h :=
  Equiv.sumCongr
    ((Equiv.prodAssoc (Fin h) (Fin 6) (Fin 2 × Fin (2 ^ h))).symm.trans
      ((Equiv.prodCongr perm (Equiv.refl (Fin 2 × Fin (2 ^ h)))).trans
        (Equiv.prodAssoc (Fin h) (Fin 6) (Fin 2 × Fin (2 ^ h)))))
    (Equiv.refl _)

@[simp] theorem relabelMarkers_sampleMarker (h : Nat) (perm : MarkerPermutation h)
    (s : ProtectionSample h) (axis : Bool) (level : Fin h) (mode : Fin 6) (group : Fin 2) :
    relabelMarkers h perm (sampleMarker h s axis level mode group) =
      sampleMarker h s axis (perm (level, mode)).1 (perm (level, mode)).2 group := rfl

theorem relabelMarkers_nonMarker (h : Nat) (perm : MarkerPermutation h)
    (p : PhysicalPosition h) (hn : NonMarker (physicalBlock h p)) :
    relabelMarkers h perm p = p := by
  rcases p with ⟨d, mode, group, offset⟩ | p
  · exact False.elim hn
  · rfl

def permutedGadgetOrder (h : Nat) (perms : Bool → MarkerPermutation h) : GadgetOrder h where
  before := fun axis p q => physicalBefore h axis
    (relabelMarkers h (perms axis) p) (relabelMarkers h (perms axis) q)
  marker_group := by
    intro s axis level mode
    simp only [relabelMarkers_sampleMarker]
    exact (canonicalGadgetOrder h).marker_group s axis _ _
  marker_body := by
    intro s axis level mode group p hn
    rw [relabelMarkers_sampleMarker, relabelMarkers_nonMarker h (perms axis) p hn]
    exact marker_before_nonMarker h s axis _ _ group p hn
  body_order := by
    intro axis p q hp hq ho
    rwa [relabelMarkers_nonMarker h (perms axis) p hp,
      relabelMarkers_nonMarker h (perms axis) q hq]

theorem permuted_arbitrary_edit_lower_bound (h : Nat) (hh : 0 < h)
    (perms : Bool → MarkerPermutation h) (matrix : PhysicalMatrix h)
    (free : IsOrderedPhysicalFree h (permutedGadgetOrder h perms) matrix) :
    (2 ^ h) ^ 2 ≤ editCount h (physicalMatrix h false) matrix :=
  ordered_arbitrary_edit_lower_bound h (permutedGadgetOrder h perms) hh matrix free

noncomputable def permutedPhysicalIndex (h : Nat) (perms : Bool → MarkerPermutation h)
    (axis : Axis) : Fin (hostSideLength h) ≃ PhysicalPosition h :=
  (physicalIndex h axis).trans (relabelMarkers h (perms (axis == .row))).symm

theorem permutedPhysicalIndex_before (h : Nat) (perms : Bool → MarkerPermutation h)
    (axis : Axis) (i j : Fin (hostSideLength h)) :
    (permutedGadgetOrder h perms).before (axis == .row)
      (permutedPhysicalIndex h perms axis i) (permutedPhysicalIndex h perms axis j) ↔ i < j := by
  change physicalBefore h (axis == .row)
    (relabelMarkers h (perms (axis == .row)) ((relabelMarkers h (perms (axis == .row))).symm
      (physicalIndex h axis i)))
    (relabelMarkers h (perms (axis == .row)) ((relabelMarkers h (perms (axis == .row))).symm
      (physicalIndex h axis j))) ↔ i < j
  simp only [Equiv.apply_symm_apply]
  exact physicalIndex_before h axis i j

noncomputable def indexPermutedMatrix (h : Nat) (perms : Bool → MarkerPermutation h)
    (matrix : PhysicalMatrix h) : BinaryMatrix (hostSideLength h) :=
  fun i j => matrix (permutedPhysicalIndex h perms .row i) (permutedPhysicalIndex h perms .column j)

noncomputable def physicalizePermutedMatrix (h : Nat) (perms : Bool → MarkerPermutation h)
    (matrix : BinaryMatrix (hostSideLength h)) : PhysicalMatrix h :=
  fun r c => matrix ((permutedPhysicalIndex h perms .row).symm r)
    ((permutedPhysicalIndex h perms .column).symm c)

@[simp] theorem indexPermutedMatrix_physicalize (h : Nat) (perms : Bool → MarkerPermutation h)
    (matrix : BinaryMatrix (hostSideLength h)) :
    indexPermutedMatrix h perms (physicalizePermutedMatrix h perms matrix) = matrix := by
  funext i j
  simp [indexPermutedMatrix, physicalizePermutedMatrix]

theorem indexPermutedMatrix_copy_iff (h : Nat) (perms : Bool → MarkerPermutation h)
    (matrix : PhysicalMatrix h) (rows cols : Fin 4 → Fin (hostSideLength h)) :
    IsMatrixCopy (indexPermutedMatrix h perms matrix) rows cols ↔
    IsOrderedPhysicalCopy h (permutedGadgetOrder h perms) matrix
      (fun i => permutedPhysicalIndex h perms .row (rows i))
      (fun j => permutedPhysicalIndex h perms .column (cols j)) := by
  constructor
  · intro hc
    exact ⟨fun i j hij => (permutedPhysicalIndex_before h perms .row _ _).mpr (hc.1 hij),
      fun i j hij => (permutedPhysicalIndex_before h perms .column _ _).mpr (hc.2.1 hij), hc.2.2⟩
  · intro hc
    exact ⟨fun i j hij => (permutedPhysicalIndex_before h perms .row _ _).mp (hc.1 i j hij),
      fun i j hij => (permutedPhysicalIndex_before h perms .column _ _).mp (hc.2.1 i j hij), hc.2.2⟩

theorem indexPermutedMatrix_free_iff (h : Nat) (perms : Bool → MarkerPermutation h)
    (matrix : PhysicalMatrix h) :
    IsMatrixFree (indexPermutedMatrix h perms matrix) ↔
      IsOrderedPhysicalFree h (permutedGadgetOrder h perms) matrix := by
  constructor
  · intro hf rows cols hc
    apply hf (fun i => (permutedPhysicalIndex h perms .row).symm (rows i))
      (fun j => (permutedPhysicalIndex h perms .column).symm (cols j))
    apply (indexPermutedMatrix_copy_iff h perms matrix _ _).mpr
    simpa only [Equiv.apply_symm_apply] using hc
  · intro hf rows cols hc
    exact hf _ _ ((indexPermutedMatrix_copy_iff h perms matrix rows cols).mp hc)

theorem indexPermutedMatrix_edit_count (h : Nat) (perms : Bool → MarkerPermutation h)
    (a b : PhysicalMatrix h) :
    matrixEditCount (indexPermutedMatrix h perms a) (indexPermutedMatrix h perms b) =
      editCount h a b := by
  unfold matrixEditCount editCount editCells
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    ((Equiv.prodCongr (permutedPhysicalIndex h perms .row)
      (permutedPhysicalIndex h perms .column)).subtypeEquiv (fun _ => Iff.rfl))

theorem permuted_matrix_edit_lower_bound (h : Nat) (hh : 0 < h)
    (perms : Bool → MarkerPermutation h) (matrix : BinaryMatrix (hostSideLength h))
    (free : IsMatrixFree matrix) :
    2 ^ (2 * h) ≤ matrixEditCount (indexPermutedMatrix h perms (physicalMatrix h false)) matrix := by
  rw [← indexPermutedMatrix_physicalize h perms matrix, indexPermutedMatrix_edit_count]
  rw [← canonicalRepairCellCount_eq_power h]
  exact permuted_arbitrary_edit_lower_bound h hh perms _
    ((indexPermutedMatrix_free_iff h perms _).mp (by simpa using free))

theorem permuted_matrix_minimum_edit_lower_bound (h : Nat) (hh : 0 < h)
    (perms : Bool → MarkerPermutation h) :
    2 ^ (2 * h) ≤ minimumMatrixEditCount (indexPermutedMatrix h perms (physicalMatrix h false)) := by
  obtain ⟨matrix, hf, he⟩ :=
    minimumMatrixEditCount_spec (indexPermutedMatrix h perms (physicalMatrix h false))
  rw [← he]
  exact permuted_matrix_edit_lower_bound h hh perms matrix hf

end H4Formal
