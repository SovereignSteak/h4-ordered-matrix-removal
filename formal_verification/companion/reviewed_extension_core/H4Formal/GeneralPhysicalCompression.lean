import H4Formal.GeneralCompression
import H4Formal.IndexedMatrixCore

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

def TwinFreePattern {k : Nat} (patt : Fin k → Fin k → Bool) : Prop :=
  Function.Injective (fun i => patt i) ∧ Function.Injective (fun j i => patt i j)

def IsPhysicalPatternCopy {k : Nat} (h : Nat) (patt : Fin k → Fin k → Bool)
    (matrix : PhysicalMatrix h) (rows cols : Fin k → PhysicalPosition h) : Prop :=
  (∀ i j, i.val < j.val → physicalBefore h true (rows i) (rows j)) ∧
  (∀ i j, i.val < j.val → physicalBefore h false (cols i) (cols j)) ∧
  (∀ i j, matrix (rows i) (cols j) = patt i j)

theorem valid_block_has_physical_representative (h : Nat) (b : Block)
    (hv : validBlock h b = true) : ∃ p : PhysicalPosition h, physicalBlock h p = b := by
  cases b with
  | anchor mode group =>
      have hb := hv
      simp only [validBlock, Bool.and_eq_true, decide_eq_true_eq,
        Bool.or_eq_true, beq_iff_eq] at hb
      have hd : 1 ≤ mode.depth ∧ mode.depth ≤ h := hb.1.1
      have hg : group = 1 ∨ group = 2 := hb.1.2
      have hm := mode_code_le_five_of_allowed mode hb.2
      refine ⟨.inl (⟨mode.depth - 1, by omega⟩,
        ⟨modeCode mode, by omega⟩, ⟨group - 1, by omega⟩,
        ⟨0, Nat.two_pow_pos h⟩), ?_⟩
      simp only [physicalBlock]
      rw [Nat.sub_add_cancel hd.1, mode_code_roundtrip mode hb.2,
        Nat.sub_add_cancel (by omega : 1 ≤ group)]
  | «variable» d p sign =>
      have hs := valid_variable_sign hv
      have hn := valid_variable_node hv
      have hd : d ≤ h := hs.1
      by_cases ht : d = h
      · have he : sign = .leaf := by simpa only [if_pos ht] using hs.2
        subst d
        subst sign
        exact ⟨.inr (.inr (.inl ⟨p, hn⟩)), rfl⟩
      · have hsign : sign = .plus ∨ sign = .minus := by
          simpa only [if_neg ht] using hs.2
        have hp : p * 2 ^ (h - d) < 2 ^ h := by
          rw [level_factor h d hd]
          exact Nat.mul_lt_mul_of_pos_right hn (Nat.two_pow_pos _)
        rcases hsign with rfl | rfl
        · refine ⟨.inr (.inl (⟨d, by omega⟩, 0, ⟨p * 2 ^ (h - d), hp⟩)), ?_⟩
          simp [physicalBlock]
        · refine ⟨.inr (.inl (⟨d, by omega⟩, 1, ⟨p * 2 ^ (h - d), hp⟩)), ?_⟩
          simp [physicalBlock]
  | dummy => exact ⟨.inr (.inr (.inr ⟨0, Nat.two_pow_pos h⟩)), rfl⟩

theorem physical_pattern_to_quotient {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (ht : TwinFreePattern patt)
    (rows cols : Fin k → PhysicalPosition h)
    (hc : IsPhysicalPatternCopy h patt (physicalMatrix h repair) rows cols) :
    IsValidPatternCopy h repair patt (fun i => physicalBlock h (rows i))
      (fun j => physicalBlock h (cols j)) := by
  have hr : Function.Injective (fun i => physicalBlock h (rows i)) := by
    intro i j he
    apply ht.1
    funext t
    exact (hc.2.2 i t).symm.trans ((congrArg
      (fun b => (concreteHost h repair).value b (physicalBlock h (cols t))) he).trans
        (hc.2.2 j t))
  have hcol : Function.Injective (fun j => physicalBlock h (cols j)) := by
    intro i j he
    apply ht.2
    funext t
    exact (hc.2.2 t i).symm.trans ((congrArg
      (fun b => (concreteHost h repair).value (physicalBlock h (rows t)) b) he).trans
        (hc.2.2 t j))
  refine ⟨?_, ?_, ?_, hc.2.2⟩
  · intro b hb
    simp only [patternRecords, List.mem_append, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> apply physicalBlock_valid
  · intro i j hij
    rcases hc.1 i j hij with he | ho
    · have := hr he.1
      subst j
      omega
    · exact ho
  · intro i j hij
    rcases hc.2.1 i j hij with he | ho
    · have := hcol he.1
      subst j
      omega
    · exact ho

theorem quotient_pattern_has_physical_copy {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (rows cols : Fin k → Block)
    (hc : IsValidPatternCopy h repair patt rows cols) :
    ∃ rows' cols', IsPhysicalPatternCopy h patt (physicalMatrix h repair) rows' cols' := by
  have hr (i : Fin k) : ∃ p, physicalBlock h p = rows i :=
    valid_block_has_physical_representative h _
      (hc.1 _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have hcol (j : Fin k) : ∃ p, physicalBlock h p = cols j :=
    valid_block_has_physical_representative h _
      (hc.1 _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)))
  choose rows' hr using hr
  choose cols' hcol using hcol
  refine ⟨rows', cols', ?_, ?_, ?_⟩
  · intro i j hij
    apply Or.inr
    rw [hr, hr]
    exact hc.2.1 i j hij
  · intro i j hij
    apply Or.inr
    rw [hcol, hcol]
    exact hc.2.2.1 i j hij
  · intro i j
    simpa only [physicalMatrix, hr, hcol] using hc.2.2.2 i j


theorem physical_pattern_exists_iff_quotient {k : Nat} (h : Nat) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (ht : TwinFreePattern patt) :
    (∃ rows cols, IsPhysicalPatternCopy h patt (physicalMatrix h repair) rows cols) ↔
      ∃ rows cols, IsValidPatternCopy h repair patt rows cols := by
  constructor
  · rintro ⟨rows, cols, hc⟩
    exact ⟨_, _, physical_pattern_to_quotient h repair patt ht rows cols hc⟩
  · rintro ⟨rows, cols, hc⟩
    exact quotient_pattern_has_physical_copy h repair patt rows cols hc

theorem physical_pattern_copy_has_small_witness {k : Nat} (hk : 0 < k)
    (h : Nat) (hh : 0 < h) (repair : Bool) (patt : Fin k → Fin k → Bool)
    (ht : TwinFreePattern patt) (rows cols : Fin k → PhysicalPosition h)
    (hc : IsPhysicalPatternCopy h patt (physicalMatrix h repair) rows cols) :
    ∃ d, 1 ≤ d ∧ d ≤ 6 * k ∧ ∃ rows' cols',
      IsPhysicalPatternCopy d patt (physicalMatrix d repair) rows' cols' := by
  obtain ⟨d, hlo, hhi, r, c, hd⟩ := pattern_copy_has_small_witness hk h hh repair patt _ _
    (physical_pattern_to_quotient h repair patt ht rows cols hc)
  exact ⟨d, hlo, hhi, quotient_pattern_has_physical_copy d repair patt r c hd⟩

theorem physical_pattern_free_all_depth_iff_bounded {k : Nat} (hk : 0 < k)
    (repair : Bool) (patt : Fin k → Fin k → Bool) (ht : TwinFreePattern patt) :
    (∀ h, 0 < h → ∀ rows cols,
      ¬ IsPhysicalPatternCopy h patt (physicalMatrix h repair) rows cols) ↔
    (∀ h, 1 ≤ h → h ≤ 6 * k → ∀ rows cols,
      ¬ IsPhysicalPatternCopy h patt (physicalMatrix h repair) rows cols) := by
  constructor
  · intro hf h hlo _
    exact hf h hlo
  · intro hf h hh rows cols hc
    obtain ⟨d, hlo, hhi, r, c, hd⟩ :=
      physical_pattern_copy_has_small_witness hk h hh repair patt ht rows cols hc
    exact hf d hlo hhi r c hd

def IsMatrixPatternCopy {n k : Nat} (patt : Fin k → Fin k → Bool)
    (matrix : BinaryMatrix n) (rows cols : Fin k → Fin n) : Prop :=
  StrictMono rows ∧ StrictMono cols ∧ ∀ i j, matrix (rows i) (cols j) = patt i j

theorem indexed_pattern_copy_iff {k : Nat} (h : Nat) (patt : Fin k → Fin k → Bool)
    (matrix : PhysicalMatrix h) (rows cols : Fin k → Fin (hostSideLength h)) :
    IsMatrixPatternCopy patt (indexPhysicalMatrix h matrix) rows cols ↔
      IsPhysicalPatternCopy h patt matrix
        (fun i => physicalIndex h .row (rows i))
        (fun j => physicalIndex h .column (cols j)) := by
  constructor
  · intro hc
    exact ⟨fun i j hij => (physicalIndex_before h .row _ _).mpr (hc.1 hij),
      fun i j hij => (physicalIndex_before h .column _ _).mpr (hc.2.1 hij), hc.2.2⟩
  · intro hc
    exact ⟨fun i j hij => (physicalIndex_before h .row _ _).mp (hc.1 i j hij),
      fun i j hij => (physicalIndex_before h .column _ _).mp (hc.2.1 i j hij), hc.2.2⟩

theorem indexed_pattern_exists_iff_physical {k : Nat} (h : Nat)
    (patt : Fin k → Fin k → Bool) (matrix : PhysicalMatrix h) :
    (∃ rows cols, IsMatrixPatternCopy patt (indexPhysicalMatrix h matrix) rows cols) ↔
      ∃ rows cols, IsPhysicalPatternCopy h patt matrix rows cols := by
  constructor
  · rintro ⟨rows, cols, hc⟩
    exact ⟨_, _, (indexed_pattern_copy_iff h patt matrix rows cols).mp hc⟩
  · rintro ⟨rows, cols, hc⟩
    refine ⟨fun i => (physicalIndex h .row).symm (rows i),
      fun j => (physicalIndex h .column).symm (cols j), ?_⟩
    apply (indexed_pattern_copy_iff h patt matrix _ _).mpr
    simpa only [Equiv.apply_symm_apply] using hc

theorem matrix_pattern_copy_has_small_witness {k : Nat} (hk : 0 < k)
    (h : Nat) (hh : 0 < h) (repair : Bool) (patt : Fin k → Fin k → Bool)
    (ht : TwinFreePattern patt) (rows cols : Fin k → Fin (hostSideLength h))
    (hc : IsMatrixPatternCopy patt (indexPhysicalMatrix h (physicalMatrix h repair)) rows cols) :
    ∃ d, 1 ≤ d ∧ d ≤ 6 * k ∧ ∃ rows' cols',
      IsMatrixPatternCopy patt (indexPhysicalMatrix d (physicalMatrix d repair)) rows' cols' := by
  obtain ⟨d, hlo, hhi, r, c, hd⟩ := physical_pattern_copy_has_small_witness hk h hh repair patt ht
    _ _ ((indexed_pattern_copy_iff h patt _ rows cols).mp hc)
  exact ⟨d, hlo, hhi, (indexed_pattern_exists_iff_physical d patt _).mpr ⟨r, c, hd⟩⟩

theorem matrix_pattern_free_all_depth_iff_bounded {k : Nat} (hk : 0 < k)
    (repair : Bool) (patt : Fin k → Fin k → Bool) (ht : TwinFreePattern patt) :
    (∀ h, 0 < h → ∀ rows cols,
      ¬ IsMatrixPatternCopy patt (indexPhysicalMatrix h (physicalMatrix h repair)) rows cols) ↔
    (∀ h, 1 ≤ h → h ≤ 6 * k → ∀ rows cols,
      ¬ IsMatrixPatternCopy patt (indexPhysicalMatrix h (physicalMatrix h repair)) rows cols) := by
  constructor
  · intro hf h hlo _
    exact hf h hlo
  · intro hf h hh rows cols hc
    obtain ⟨d, hlo, hhi, r, c, hd⟩ :=
      matrix_pattern_copy_has_small_witness hk h hh repair patt ht rows cols hc
    exact hf d hlo hhi r c hd


instance physicalPatternCopyDecidable {k : Nat} (h : Nat) (patt : Fin k → Fin k → Bool)
    (matrix : PhysicalMatrix h) (rows cols : Fin k → PhysicalPosition h) :
    Decidable (IsPhysicalPatternCopy h patt matrix rows cols) := by
  unfold IsPhysicalPatternCopy physicalBefore
  infer_instance

instance physicalPatternFreeDecidable {k : Nat} (h : Nat)
    (patt : Fin k → Fin k → Bool) (matrix : PhysicalMatrix h) :
    Decidable (∀ rows cols, ¬ IsPhysicalPatternCopy h patt matrix rows cols) := by
  letI (rows : Fin k → PhysicalPosition h) :
      Decidable (∀ cols, ¬ IsPhysicalPatternCopy h patt matrix rows cols) :=
    Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

def boundedPhysicalPatternFree {k : Nat} (repair : Bool) (patt : Fin k → Fin k → Bool) : Bool :=
  decide (∀ d : Fin (6 * k), ∀ rows cols,
    ¬ IsPhysicalPatternCopy (d.val + 1) patt (physicalMatrix (d.val + 1) repair) rows cols)

theorem boundedPhysicalPatternFree_correct {k : Nat} (hk : 0 < k) (repair : Bool)
    (patt : Fin k → Fin k → Bool) (ht : TwinFreePattern patt) :
    boundedPhysicalPatternFree repair patt = true ↔
      ∀ h, 0 < h → ∀ rows cols,
        ¬ IsPhysicalPatternCopy h patt (physicalMatrix h repair) rows cols := by
  rw [physical_pattern_free_all_depth_iff_bounded hk repair patt ht]
  unfold boundedPhysicalPatternFree
  rw [decide_eq_true_eq]
  constructor
  · intro hf h hlo hhi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    exact hf ⟨d, by omega⟩
  · intro hf d
    exact hf (d.val + 1) (by omega) (by have := d.isLt; omega)

end H4Formal
