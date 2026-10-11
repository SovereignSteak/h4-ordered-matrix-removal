import H4Formal.Pattern
import H4Formal.Host

/-!
# Local-to-global logical interface

This file certifies the *logical step* from preservation of selected order
relations and all 16 entries to preservation of an induced H4 copy.

The constructor `CopyEmbedding` explicitly requires those preservation facts.
It does not construct the embedding of the paper, and should never be cited
as a proof of the 24-level depth-compression theorem in isolation.
-/

namespace H4Formal

structure OrderedBlockHost where
  value : Block → Block → Bool
  rowBefore : Block → Block → Prop
  colBefore : Block → Block → Prop

/-- An ordered, induced four-by-four copy of the fixed pattern. -/
def IsCopy (H : OrderedBlockHost) (rows cols : Fin 4 → Block) : Prop :=
  (∀ i j : Fin 4, i.val < j.val → H.rowBefore (rows i) (rows j)) ∧
  (∀ i j : Fin 4, i.val < j.val → H.colBefore (cols i) (cols j)) ∧
  (∀ i j : Fin 4, H.value (rows i) (cols j) = pattern i j)

structure CopyEmbedding (H K : OrderedBlockHost) where
  mapRow : Block → Block
  mapCol : Block → Block
  rowOrder : ∀ r s, H.rowBefore r s → K.rowBefore (mapRow r) (mapRow s)
  colOrder : ∀ c d, H.colBefore c d → K.colBefore (mapCol c) (mapCol d)
  entries : ∀ r c, K.value (mapRow r) (mapCol c) = H.value r c

/-- No SMT premise occurs in this transfer theorem. -/
theorem transfer_copy (H K : OrderedBlockHost) (e : CopyEmbedding H K)
    (rows cols : Fin 4 → Block) (hc : IsCopy H rows cols) :
    IsCopy K (fun i => e.mapRow (rows i)) (fun i => e.mapCol (cols i)) := by
  constructor
  · intro i j hij
    exact e.rowOrder _ _ (hc.1 i j hij)
  constructor
  · intro i j hij
    exact e.colOrder _ _ (hc.2.1 i j hij)
  · intro i j
    calc
      K.value (e.mapRow (rows i)) (e.mapCol (cols j)) =
          H.value (rows i) (cols j) := e.entries _ _
      _ = pattern i j := hc.2.2 i j

/-- Transfer of pattern-freeness follows contravariantly. -/
theorem free_of_embedding (H K : OrderedBlockHost) (e : CopyEmbedding H K)
    (hfree : ∀ rows cols, ¬ IsCopy K rows cols) :
    ∀ rows cols, ¬ IsCopy H rows cols := by
  intro rows cols hc
  exact hfree _ _ (transfer_copy H K e rows cols hc)

end H4Formal
