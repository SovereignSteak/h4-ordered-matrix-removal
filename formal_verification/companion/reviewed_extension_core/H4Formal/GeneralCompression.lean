import H4Formal.HostOrderCompression

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem compression_depth_le_six_k (h k : Nat) (hk : 0 < k) (selected : List Block)
    (hs : selected.length ≤ 2 * k) :
    retainedDepth (compressionLevels h selected) h ≤ 6 * k := by
  have hsorted := actualRetainedLevels_sorted h (blockLevels selected) (blockWords selected)
  have hn := hsorted.imp (by intro a b hab; exact Nat.ne_of_lt hab)
  have hz := actualRetainedLevels_mem h (blockLevels selected) (blockWords selected) (Or.inl rfl)
  have hc := retainedDepth_le_card _ hn hz h
  have hb := actualRetainedLevels_length_bound h (blockLevels selected) (blockWords selected)
  have hd : (blockLevels selected).length ≤ selected.length := List.length_filterMap_le _ _
  have hw : (blockWords selected).length ≤ selected.length := List.length_filterMap_le _ _
  change retainedDepth (actualRetainedLevels h (blockLevels selected) (blockWords selected)) h ≤ _
  omega

def patternRecords {k : Nat} (rows cols : Fin k → Block) : List Block :=
  List.ofFn rows ++ List.ofFn cols

def IsValidPatternCopy {k : Nat} (h : Nat) (repair : Bool) (patt : Fin k → Fin k → Bool)
    (rows cols : Fin k → Block) : Prop :=
  (∀ b ∈ patternRecords rows cols, validBlock h b = true) ∧
    (∀ i j, i.val < j.val → hostComesBefore true true (rows i) (rows j) = true) ∧
    (∀ i j, i.val < j.val → hostComesBefore true false (cols i) (cols j) = true) ∧
    (∀ i j, (concreteHost h repair).value (rows i) (cols j) = patt i j)

theorem pattern_copy_compress {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (rows cols : Fin k → Block)
    (hc : IsValidPatternCopy h repair patt rows cols) :
    let levels := compressionLevels h (patternRecords rows cols)
    IsValidPatternCopy (retainedDepth levels h) repair patt
      (fun i => compressBlock levels (rows i)) (fun i => compressBlock levels (cols i)) := by
  let selected := patternRecords rows cols
  let levels := compressionLevels h selected
  have hv : ∀ b ∈ selected, validBlock h b = true := hc.1
  have hr (i : Fin k) : rows i ∈ selected :=
    List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hcol (i : Fin k) : cols i ∈ selected :=
    List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  constructor
  · intro b hb
    simp only [patternRecords, List.mem_append, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact validBlock_compress h selected hv (hr i)
    · exact validBlock_compress h selected hv (hcol i)
  constructor
  · intro i j hij
    rw [hostComesBefore_compress h selected hv (hr i) (hr j)]
    exact hc.2.1 i j hij
  constructor
  · intro i j hij
    rw [hostComesBefore_compress h selected hv (hcol i) (hcol j)]
    exact hc.2.2.1 i j hij
  · intro i j
    cases repair
    · change hostValue (retainedDepth levels h) _ _ = patt i j
      rw [hostValue_compress h selected hv (hr i) (hcol j)]
      exact hc.2.2.2 i j
    · change repairedValue (retainedDepth levels h) _ _ = patt i j
      rw [repairedValue_compress h selected hv (hr i) (hcol j)]
      exact hc.2.2.2 i j

theorem pattern_copy_has_small_witness {k : Nat} (hk : 0 < k) (h : Nat) (hh : 0 < h)
    (repair : Bool) (patt : Fin k → Fin k → Bool) (rows cols : Fin k → Block)
    (hc : IsValidPatternCopy h repair patt rows cols) :
    ∃ d, 1 ≤ d ∧ d ≤ 6 * k ∧ ∃ rows' cols', IsValidPatternCopy d repair patt rows' cols' := by
  let selected := patternRecords rows cols
  let levels := compressionLevels h selected
  have hd : 1 ≤ retainedDepth levels h := actualRetainedDepth_pos h _ _ hh
  have hu : retainedDepth levels h ≤ 6 * k :=
    compression_depth_le_six_k h k hk selected (by simp [selected, patternRecords, Nat.two_mul])
  exact ⟨retainedDepth levels h, hd, hu, (fun i => compressBlock levels (rows i)),
    (fun i => compressBlock levels (cols i)), pattern_copy_compress h repair patt rows cols hc⟩

theorem pattern_free_all_depth_iff_bounded {k : Nat} (hk : 0 < k) (repair : Bool)
    (patt : Fin k → Fin k → Bool) :
    (∀ h : Nat, 0 < h → ∀ rows cols, ¬ IsValidPatternCopy h repair patt rows cols) ↔
      (∀ h : Nat, 1 ≤ h → h ≤ 6 * k → ∀ rows cols, ¬ IsValidPatternCopy h repair patt rows cols) := by
  constructor
  · intro hf h hlo _ rows cols
    exact hf h (by omega) rows cols
  · intro hf h hh rows cols hc
    obtain ⟨d, hlo, hhi, rows', cols', hc'⟩ :=
      pattern_copy_has_small_witness hk h hh repair patt rows cols hc
    exact hf d hlo hhi rows' cols' hc'

end H4Formal
