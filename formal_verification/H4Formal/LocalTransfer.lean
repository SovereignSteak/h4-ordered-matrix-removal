import H4Formal.ValidHost

namespace H4Formal

/-- Order and entry preservation on four selected row and column types. -/
structure SelectedCopyEmbedding (H K : OrderedBlockHost)
    (rows cols rows' cols' : Fin 4 → Block) where
  rowOrder : ∀ i j, H.rowBefore (rows i) (rows j) → K.rowBefore (rows' i) (rows' j)
  colOrder : ∀ i j, H.colBefore (cols i) (cols j) → K.colBefore (cols' i) (cols' j)
  entries : ∀ i j, K.value (rows' i) (cols' j) = H.value (rows i) (cols j)

theorem transfer_selected_copy (H K : OrderedBlockHost)
    (rows cols rows' cols' : Fin 4 → Block)
    (e : SelectedCopyEmbedding H K rows cols rows' cols')
    (hc : IsCopy H rows cols) : IsCopy K rows' cols' := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact e.rowOrder i j (hc.1 i j hij)
  · intro i j hij
    exact e.colOrder i j (hc.2.1 i j hij)
  · intro i j
    exact (e.entries i j).trans (hc.2.2 i j)

theorem transfer_selected_valid_copy (h h' : Nat) (H K : OrderedBlockHost)
    (rows cols rows' cols' : Fin 4 → Block)
    (e : SelectedCopyEmbedding H K rows cols rows' cols')
    (hr : ∀ i, ValidBlock h' (rows' i)) (hc' : ∀ j, ValidBlock h' (cols' j))
    (hc : ValidCopy h H rows cols) : ValidCopy h' K rows' cols' := by
  exact ⟨hr, hc', transfer_selected_copy H K rows cols rows' cols' e hc.2.2⟩

end H4Formal
