import H4Formal

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#print axioms H4Formal.blockBefore_irrefl
#print axioms H4Formal.transfer_selected_valid_copy
#print axioms H4Formal.terminalI_validCopy
#print axioms H4Formal.terminalII_validCopy
#print axioms H4Formal.physical_free_iff_quotient_free
#print axioms H4Formal.protected_path_not_free
#print axioms H4Formal.finite_union_bound
#print axioms H4Formal.exists_unhit_sample_uniform
#print axioms H4Formal.sample_row_marker_injective
#print axioms H4Formal.sample_marker_column_injective
#print axioms H4Formal.protected_cell_sample_injective
#print axioms H4Formal.exists_protected_selection
#print axioms H4Formal.vPlus_frame
#print axioms H4Formal.vMinus_frame
#print axioms H4Formal.wPlus_frame
#print axioms H4Formal.wMinus_frame
#print axioms H4Formal.selectionProtectedPath
#print axioms H4Formal.arbitrary_edit_lower_bound
#print axioms H4Formal.classification_exhaustive
#print axioms H4Formal.classification_iff
#print axioms H4Formal.canonical_standard_free
#print axioms H4Formal.exact_copy_count
#print axioms H4Formal.exact_edit_distance
#print axioms H4Formal.orderedPosition_order_iff
#print axioms H4Formal.normalized_copy_ratio_tendsto
#print axioms H4Formal.no_polynomial_removal_bound
#print axioms H4Formal.end_to_end_main_theorem

#check H4Formal.arbitrary_edit_lower_bound
#check H4Formal.end_to_end_main_theorem

example : H4Formal.hostCopyCount 1 = 128 := by
  rw [H4Formal.exact_copy_count 1 (by decide)]
  norm_num

example : H4Formal.hostCopyCount 2 = 9216 := by
  rw [H4Formal.exact_copy_count 2 (by decide)]
  norm_num

example : H4Formal.editDistance (H4Formal.standardHost 1) = 4 := by
  simpa using H4Formal.exact_edit_distance 1 (by decide)

example : H4Formal.distanceDensity 1 = (1 : Real) / 256 := by
  rw [H4Formal.exact_normalized_distance 1 (by decide)]
  norm_num [H4Formal.epsilon]

example : H4Formal.ValidCopy 3 (H4Formal.originalHost 3)
    (H4Formal.terminalRows 3 5) (H4Formal.terminalIColumns 3 5) :=
  H4Formal.terminalI_validCopy 3 5 (by decide) (by decide)

example : H4Formal.ValidCopy 3 (H4Formal.originalHost 3)
    (H4Formal.terminalRows 3 5) (H4Formal.terminalIIColumns 3 5 1) :=
  H4Formal.terminalII_validCopy 3 5 1 (by decide) (by decide) (by decide) (by decide)
