import H4Formal.Compression
import H4Formal.CompressionRelations
import H4Formal.Transfer

namespace H4Formal

def properPrefix (u v : BinaryWord) : Prop :=
  u <+: v ∧ u.length < v.length

def bitLT (a b : Bool) : Prop := a = false ∧ b = true

def binaryLexLess (u v : BinaryWord) : Prop :=
  List.Lex bitLT u v

def firstDivergence (u v : BinaryWord) : Option Nat :=
  firstDifference u v

def endpointBit (u : BinaryWord) : Option Bool :=
  u.getLast?

def parentWord (u : BinaryWord) : BinaryWord :=
  u.dropLast

def equalDepthNumericLess (u v : BinaryWord) : Prop :=
  u.length = v.length ∧ binaryLexLess u v

structure WordCompressionWitness where
  map : BinaryWord → BinaryWord
  depthMap : Nat → Nat
  length_map : ∀ u, (map u).length = depthMap u.length
  depth_order : ∀ a b, depthMap a = depthMap b ↔ a = b
  prefix_iff : ∀ u v, (map u <+: map v) ↔ u <+: v
  length_lt_iff : ∀ u v, (map u).length < (map v).length ↔ u.length < v.length
  lex_iff : ∀ u v, binaryLexLess (map u) (map v) ↔ binaryLexLess u v
  first_divergence_defined_iff : ∀ u v,
    (∃ d, firstDivergence (map u) (map v) = some d) ↔
      ∃ d, firstDivergence u v = some d
  endpoint_iff : ∀ u, endpointBit (map u) = endpointBit u
  parent_iff : ∀ u, parentWord (map u) = map (parentWord u)

theorem WordCompressionWitness.properPrefix_iff
    (w : WordCompressionWitness) (u v : BinaryWord) :
    properPrefix (w.map u) (w.map v) ↔ properPrefix u v := by
  simp [properPrefix, w.prefix_iff, w.length_lt_iff]

theorem WordCompressionWitness.firstDivergence_defined_preserved
    (w : WordCompressionWitness) (u v : BinaryWord) :
    (∃ d, firstDivergence (w.map u) (w.map v) = some d) ↔
      ∃ d, firstDivergence u v = some d := by
  exact w.first_divergence_defined_iff u v

theorem WordCompressionWitness.lex_preserved
    (w : WordCompressionWitness) (u v : BinaryWord) :
    binaryLexLess (w.map u) (w.map v) ↔ binaryLexLess u v := by
  exact w.lex_iff u v

theorem WordCompressionWitness.endpoint_preserved
    (w : WordCompressionWitness) (u : BinaryWord) :
    endpointBit (w.map u) = endpointBit u := by
  exact w.endpoint_iff u

theorem WordCompressionWitness.parent_preserved
    (w : WordCompressionWitness) (u : BinaryWord) :
    parentWord (w.map u) = w.map (parentWord u) := by
  exact w.parent_iff u

theorem WordCompressionWitness.equalDepthNumericLess_preserved
    (w : WordCompressionWitness) (u v : BinaryWord) :
    equalDepthNumericLess (w.map u) (w.map v) ↔
      equalDepthNumericLess u v := by
  simp [equalDepthNumericLess, w.length_map, w.depth_order, w.lex_iff]

structure OrderedCompressionTransfer where
  original : OrderedBlockHost
  compressed : OrderedBlockHost
  mapRow : Block → Block
  mapCol : Block → Block
  row_order : ∀ r s,
    original.rowBefore r s → compressed.rowBefore (mapRow r) (mapRow s)
  col_order : ∀ c d,
    original.colBefore c d → compressed.colBefore (mapCol c) (mapCol d)
  entries : ∀ r c,
    compressed.value (mapRow r) (mapCol c) = original.value r c

def OrderedCompressionTransfer.asEmbedding
    (t : OrderedCompressionTransfer) : CopyEmbedding t.original t.compressed :=
  { mapRow := t.mapRow
    mapCol := t.mapCol
    rowOrder := t.row_order
    colOrder := t.col_order
    entries := t.entries }

theorem OrderedCompressionTransfer.transfer
    (t : OrderedCompressionTransfer) (rows cols : Fin 4 → Block)
    (hc : IsCopy t.original rows cols) :
    IsCopy t.compressed (fun i => t.mapRow (rows i))
      (fun i => t.mapCol (cols i)) := by
  exact transfer_copy t.original t.compressed t.asEmbedding rows cols hc

end H4Formal
