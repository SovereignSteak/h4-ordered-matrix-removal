import H4Formal.Pattern
import H4Formal.Host

/-!
# Ordered copy transfer

Embeddings preserve both axis orders and all matrix entries. Induced copies
transfer along an embedding, and pattern freeness transfers contravariantly.
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

/-- An order- and entry-preserving embedding transfers induced copies. -/
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
