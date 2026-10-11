import H4Formal.GlobalCounting
import H4Formal.FiniteAvoidance

namespace H4Formal.ExactTransversal

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev Cell (h : Nat) := PhysicalPosition h × PhysicalPosition h

def ContainsCell {h : Nat} (r c : Fin 4 → PhysicalPosition h) (e : Cell h) : Prop :=
  ∃ i j, r i = e.1 ∧ c j = e.2

/-- A list hits every original induced ordered physical H4 copy.
The minimum is attained by a duplicate-free list; the lower bound allows
arbitrary lists and therefore also covers every finite set of cells. -/
def HitsAll (h : Nat) (cells : List (Cell h)) : Prop :=
  ∀ r c, MatrixCopy (physicalHost h) r c →
    ∃ e ∈ cells, ContainsCell r c e

def diagonalCells (h : Nat) : List (Cell h) :=
  (List.finRange (2 ^ h)).map (fun p => (leafPosition h p, leafPosition h p))

theorem diagonalCells_length (h : Nat) : (diagonalCells h).length = 2 ^ h := by
  simp [diagonalCells]

theorem diagonalCells_nodup (h : Nat) : (diagonalCells h).Nodup := by
  apply nodup_map_injective _ _ (finRange_nodup _)
  intro p q he
  apply Fin.ext
  have hb := congrArg PhysicalPosition.block (Prod.mk.inj he).1
  exact (Block.variable.inj hb).2.1

theorem eq_leaf_of_block (h : Nat) (p : Fin (2 ^ h)) (x : PhysicalPosition h)
    (hb : x.block = .variable h p.val .leaf) : x = leafPosition h p := by
  apply physicalPosition_ext x (leafPosition h p) hb
  have hx := x.offset_lt
  rw [hb] at hx
  have hz : x.offset = 0 := by simpa [blockSize] using hx
  exact hz

theorem diagonalCells_hits_of_exhaustion (h : Nat) (hex : TerminalExhaustion h) :
    HitsAll h (diagonalCells h) := by
  intro r c hc
  have hq : ValidCopy h (originalHost h) (fun i => (r i).block) (fun i => (c i).block) := by
    simpa only [quotientHost] using physical_copy_projects h false r c hc
  obtain ⟨p, hp, hr, hcols⟩ := hex _ _ hq
  let pp : Fin (2 ^ h) := ⟨p, hp⟩
  have hrow : r 2 = leafPosition h pp := by
    apply eq_leaf_of_block
    exact congrFun hr 2
  have hcol : c 2 = leafPosition h pp := by
    apply eq_leaf_of_block
    rcases hcols with hI | ⟨q, _, _, hII⟩
    · exact congrFun hI 2
    · exact congrFun hII 2
  refine ⟨(leafPosition h pp, leafPosition h pp), ?_, 2, 2, hrow, hcol⟩
  exact List.mem_map.mpr ⟨pp, finRange_mem _ _, rfl⟩

def packedAnchor (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h))
    (g : Nat) (hg : g = 1 ∨ g = 2) : PhysicalPosition h :=
  ⟨.anchor (terminalMode h p.val) g, ⟨terminalMode_valid h p.val hh, hg⟩, p.val, p.isLt⟩

def packedParent (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) : PhysicalPosition h :=
  ⟨.variable (h - 1) (p.val / 2) .minus, terminal_parent_valid h p.val hh p.isLt,
    p.val % 2, by
      have hd : h - (h - 1) = 1 := by omega
      simpa [blockSize, hd] using Nat.mod_lt p.val (by decide : 0 < 2)⟩

def packedRows (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) : Fin 4 → PhysicalPosition h :=
  four (packedAnchor h hh p 1 (Or.inl rfl))
    (packedAnchor h hh p 2 (Or.inr rfl)) (leafPosition h p) (dummyPosition h p)

def packedCols (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) : Fin 4 → PhysicalPosition h :=
  four (packedAnchor h hh p 1 (Or.inl rfl))
    (packedAnchor h hh p 2 (Or.inr rfl)) (leafPosition h p) (packedParent h hh p)

theorem packed_copy (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) :
    MatrixCopy (physicalHost h) (packedRows h hh p) (packedCols h hh p) := by
  apply valid_copy_arbitrary_offsets
  have hr : (fun i => (packedRows h hh p i).block) = terminalRows h p.val := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 => rfl
    | n + 4 => omega
  have hc : (fun i => (packedCols h hh p i).block) = terminalIColumns h p.val := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 => rfl
    | n + 4 => omega
  rw [hr, hc]
  simpa only [quotientHost] using terminalI_validCopy h p.val hh p.isLt

/-- Each row of the p-th packed copy alone recovers p. -/
def rowOwner {h : Nat} (x : PhysicalPosition h) : Nat :=
  match x.block with
  | .variable _ p .leaf => p
  | _ => x.offset

theorem packed_row_owner (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) (i : Fin 4) :
    rowOwner (packedRows h hh p i) = p.val := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | n + 4 => omega

theorem packed_cell_unique (h : Nat) (hh : 1 ≤ h) (p q : Fin (2 ^ h)) (e : Cell h)
    (hp : ContainsCell (packedRows h hh p) (packedCols h hh p) e)
    (hq : ContainsCell (packedRows h hh q) (packedCols h hh q) e) : p = q := by
  obtain ⟨i, j, hr, _⟩ := hp
  obtain ⟨i', j', hr', _⟩ := hq
  apply Fin.ext
  calc
    p.val = rowOwner (packedRows h hh p i) := (packed_row_owner ..).symm
    _ = rowOwner e.1 := congrArg rowOwner hr
    _ = rowOwner (packedRows h hh q i') := congrArg rowOwner hr'.symm
    _ = q.val := packed_row_owner ..

theorem hitting_lower_bound (h : Nat) (hh : 1 ≤ h) (cells : List (Cell h))
    (hits : HitsAll h cells) : 2 ^ h ≤ cells.length := by
  classical
  apply Classical.byContradiction
  intro hn
  let hit : Cell h → Fin (2 ^ h) → Bool := fun e p =>
    decide (ContainsCell (packedRows h hh p) (packedCols h hh p) e)
  have cap : ∀ e ∈ cells, (List.finRange (2 ^ h)).countP (hit e) ≤ 1 := by
    intro e _
    apply countP_le_one_of_unique _ (finRange_nodup _)
    intro p _ q _ hp hq
    exact packed_cell_unique h hh p q e (of_decide_eq_true hp) (of_decide_eq_true hq)
  have small : cells.length * 1 < (List.finRange (2 ^ h)).length := by
    simp only [List.length_finRange, Nat.mul_one]
    omega
  obtain ⟨p, _, avoid⟩ := exists_unhit_sample (List.finRange (2 ^ h)) cells hit 1 cap small
  obtain ⟨e, he, hp⟩ := hits _ _ (packed_copy h hh p)
  have bad : hit e p = true := by exact decide_eq_true hp
  exact Bool.noConfusion ((avoid e he).symm.trans bad)

/-- The exact finite-set transversal statement, expressed by an attained
duplicate-free hitting list and a lower bound for every hitting list. -/
theorem exact_transversal_of_exhaustion (h : Nat) (hh : 1 ≤ h) (hex : TerminalExhaustion h) :
    (diagonalCells h).Nodup ∧ HitsAll h (diagonalCells h) ∧
      (diagonalCells h).length = 2 ^ h ∧
      ∀ cells : List (Cell h), HitsAll h cells → 2 ^ h ≤ cells.length := by
  exact ⟨diagonalCells_nodup h, diagonalCells_hits_of_exhaustion h hex,
    diagonalCells_length h, hitting_lower_bound h hh⟩


/-- The same hitting notion on the ordinary numerically indexed host. -/
abbrev StandardCell (h : Nat) := Fin (hostSize h) × Fin (hostSize h)

def StandardHitsAll (h : Nat) (cells : List (StandardCell h)) : Prop :=
  ∀ r c, MatrixCopy (standardHost h) r c →
    ∃ e ∈ cells, ∃ i j, r i = e.1 ∧ c j = e.2

noncomputable def indexCell (h : Nat) (e : Cell h) : StandardCell h :=
  (orderedIndex .row h e.1, orderedIndex .column h e.2)

noncomputable def unindexCell (h : Nat) (e : StandardCell h) : Cell h :=
  (orderedPosition .row h e.1, orderedPosition .column h e.2)

noncomputable def standardDiagonalCells (h : Nat) : List (StandardCell h) :=
  (diagonalCells h).map (indexCell h)

theorem indexCell_injective (h : Nat) (e f : Cell h)
    (he : indexCell h e = indexCell h f) : e = f := by
  apply Prod.ext
  · have hx := congrArg (orderedPosition .row h) (Prod.mk.inj he).1
    simpa only [indexCell, orderedPosition_orderedIndex] using hx
  · have hx := congrArg (orderedPosition .column h) (Prod.mk.inj he).2
    simpa only [indexCell, orderedPosition_orderedIndex] using hx

theorem standardDiagonalCells_nodup (h : Nat) : (standardDiagonalCells h).Nodup :=
  nodup_map_injective _ _ (diagonalCells_nodup h) (indexCell_injective h)

theorem standardDiagonalCells_length (h : Nat) :
    (standardDiagonalCells h).length = 2 ^ h := by
  simp [standardDiagonalCells, diagonalCells_length]

theorem standardDiagonalCells_hits_of_exhaustion (h : Nat) (hex : TerminalExhaustion h) :
    StandardHitsAll h (standardDiagonalCells h) := by
  intro r c hc
  have hp := (standard_copy_iff h false r c).1 hc
  obtain ⟨e, he, i, j, hr, hc⟩ := diagonalCells_hits_of_exhaustion h hex _ _ hp
  refine ⟨indexCell h e, List.mem_map.mpr ⟨e, he, rfl⟩, i, j, ?_, ?_⟩
  · have hx := congrArg (orderedIndex .row h) hr
    simpa only [indexCell, orderedIndex_orderedPosition] using hx
  · have hx := congrArg (orderedIndex .column h) hc
    simpa only [indexCell, orderedIndex_orderedPosition] using hx

theorem physical_hits_of_standard_hits (h : Nat) (cells : List (StandardCell h))
    (hits : StandardHitsAll h cells) : HitsAll h (cells.map (unindexCell h)) := by
  intro r c hc
  let rr := fun i => orderedIndex .row h (r i)
  let cc := fun i => orderedIndex .column h (c i)
  have hs : MatrixCopy (standardHost h) rr cc := by
    apply (standard_copy_iff h false rr cc).2
    simpa only [rr, cc, orderedPosition_orderedIndex] using hc
  obtain ⟨e, he, i, j, hr, hc'⟩ := hits rr cc hs
  refine ⟨unindexCell h e, List.mem_map.mpr ⟨e, he, rfl⟩, i, j, ?_, ?_⟩
  · have hx := congrArg (orderedPosition .row h) hr
    simpa only [rr, unindexCell, orderedPosition_orderedIndex] using hx
  · have hx := congrArg (orderedPosition .column h) hc'
    simpa only [cc, unindexCell, orderedPosition_orderedIndex] using hx

theorem standard_hitting_lower_bound (h : Nat) (hh : 1 ≤ h)
    (cells : List (StandardCell h)) (hits : StandardHitsAll h cells) :
    2 ^ h ≤ cells.length := by
  have hl := hitting_lower_bound h hh _ (physical_hits_of_standard_hits h cells hits)
  simpa only [List.length_map] using hl

/-- The exact attained transversal statement for ordinary Fin-indexed matrices. -/
theorem exact_standard_transversal_of_exhaustion (h : Nat) (hh : 1 ≤ h)
    (hex : TerminalExhaustion h) :
    (standardDiagonalCells h).Nodup ∧ StandardHitsAll h (standardDiagonalCells h) ∧
      (standardDiagonalCells h).length = 2 ^ h ∧
      ∀ cells : List (StandardCell h), StandardHitsAll h cells → 2 ^ h ≤ cells.length := by
  exact ⟨standardDiagonalCells_nodup h, standardDiagonalCells_hits_of_exhaustion h hex,
    standardDiagonalCells_length h, standard_hitting_lower_bound h hh⟩

end H4Formal.ExactTransversal
