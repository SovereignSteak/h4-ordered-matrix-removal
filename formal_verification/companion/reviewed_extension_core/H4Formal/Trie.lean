import H4Formal.Compression

namespace H4Formal

/-!
# Binary trie certificate

The compression argument needs one genuinely combinatorial fact: a binary
trie with v terminal records has at most v - 1 branching vertices. This
file proves that fact for an inductive trie, including the version where only
the distinct labels of branching vertices are retained. The TrieCoverage
record is the precise interface used to connect a concrete list of selected
words to the inductive trie.
-/

inductive BinaryTrie where
  | terminal
  | branch (left right : BinaryTrie)
  deriving Repr, DecidableEq

def BinaryTrie.leafCount : BinaryTrie -> Nat
  | .terminal => 1
  | .branch left right => leafCount left + leafCount right

def BinaryTrie.branchCount : BinaryTrie -> Nat
  | .terminal => 0
  | .branch left right => 1 + branchCount left + branchCount right

def BinaryTrie.branchLabels : Nat -> BinaryTrie -> List Nat
  | _, .terminal => []
  | d, .branch left right =>
      d :: (branchLabels (d + 1) left ++ branchLabels (d + 1) right)

@[simp] theorem BinaryTrie.branchLabels_length (d : Nat) (t : BinaryTrie) :
    (t.branchLabels d).length = t.branchCount := by
  induction t generalizing d with
  | terminal => rfl
  | branch left right ihl ihr =>
      simp [BinaryTrie.branchLabels, BinaryTrie.branchCount, ihl, ihr,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem BinaryTrie.branchCount_add_one_le_leafCount (t : BinaryTrie) :
    t.branchCount + 1 <= t.leafCount := by
  induction t with
  | terminal => simp [BinaryTrie.branchCount, BinaryTrie.leafCount]
  | branch left right ihl ihr =>
      simp [BinaryTrie.branchCount, BinaryTrie.leafCount] at *
      omega

theorem BinaryTrie.distinct_branch_labels_bound (d : Nat) (t : BinaryTrie) :
    (t.branchLabels d).eraseDups.length <= t.leafCount - 1 := by
  have hdedup := eraseDups_length_le (t.branchLabels d)
  have hlabels : (t.branchLabels d).length = t.branchCount :=
    t.branchLabels_length d
  have hbranches := t.branchCount_add_one_le_leafCount
  rw [hlabels] at hdedup
  omega

def firstDifferenceLevel (u v : BinaryWord) (d : Nat) : Prop :=
  firstDifference u v = some d

structure TrieCoverage (words : List BinaryWord) where
  trie : BinaryTrie
  words_nodup : words.Nodup
  leaf_count : trie.leafCount = words.length
  covers : ∀ {u v d}, u ∈ words → v ∈ words →
    firstDifferenceLevel u v d → d ∈ trie.branchLabels 0

theorem TrieCoverage.branch_level_bound
    {words : List BinaryWord} (c : TrieCoverage words) :
    (c.trie.branchLabels 0).eraseDups.length <= words.length - 1 := by
  rw [← c.leaf_count]
  exact c.trie.distinct_branch_labels_bound 0

theorem TrieCoverage.first_difference_is_retained
    {words : List BinaryWord} (c : TrieCoverage words)
    {u v : BinaryWord} {d : Nat} (hu : u ∈ words) (hv : v ∈ words)
    (hfd : firstDifferenceLevel u v d) :
    d ∈ c.trie.branchLabels 0 := by
  exact c.covers hu hv hfd

theorem trie_branch_budget_of_coverage
    {words : List BinaryWord} (c : TrieCoverage words) :
    (c.trie.branchLabels 0).eraseDups.length <= words.length - 1 := by
  exact c.branch_level_bound

end H4Formal
