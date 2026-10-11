import H4Formal.ProtectedSampling

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def pathNode (h : Nat) (s : ProtectionSample h) (d : Nat) : Nat :=
  (sampleLeaf h s).val / 2 ^ (h - d)

def pathSign (h d : Nat) (minus : Bool) : Sign :=
  if d = h then .leaf else if minus then .minus else .plus

def pathVariable (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (d : Nat) (hd : d ≤ h) (minus : Bool) : PhysicalPosition h :=
  if ht : d = h then leafPosition h (sampleLeaf h s)
  else .inr (.inl (⟨d, by omega⟩, if minus then 1 else 0,
    if d = 0 then (if isRow then s.1 else s.2) else sampleLeaf h s))

def sampleMarker (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) : PhysicalPosition h :=
  markerPosition h level mode group (if isRow then s.1 else s.2)

def sampleDummy (h : Nat) (s : ProtectionSample h) (isRow : Bool) : PhysicalPosition h :=
  dummyPosition h (if isRow then s.1 else s.2)

theorem pathNode_zero (h : Nat) (s : ProtectionSample h) : pathNode h s 0 = 0 := by
  exact Nat.div_eq_of_lt (sampleLeaf h s).isLt

theorem pathNode_parent (h : Nat) (s : ProtectionSample h) (d : Nat) (hd : d + 1 ≤ h) :
    pathNode h s (d + 1) / 2 = pathNode h s d := by
  have he : h - d = (h - (d + 1)) + 1 := by omega
  simp only [pathNode, Nat.div_div_eq_div_mul]
  rw [← Nat.pow_succ, he]

@[simp] theorem pathVariable_block (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    physicalBlock h (pathVariable h s isRow d hd minus) =
      .variable d (pathNode h s d) (pathSign h d minus) := by
  by_cases ht : d = h
  · simp [pathVariable, pathSign, pathNode, ht]
  · by_cases hz : d = 0
    · subst d
      cases isRow <;> cases minus <;>
        simp [pathVariable, physicalBlock, pathSign, ht, pathNode_zero,
          Nat.div_eq_of_lt s.1.isLt, Nat.div_eq_of_lt s.2.isLt]
    · cases minus <;>
        simp [pathVariable, physicalBlock, pathSign, pathNode, ht, hz]

@[simp] theorem sampleMarker_block (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) :
    physicalBlock h (sampleMarker h s isRow level mode group) =
      .anchor (modeFromCode mode.val (level.val + 1)) (group.val + 1) := rfl

@[simp] theorem sampleDummy_block (h : Nat) (s : ProtectionSample h) (isRow : Bool) :
    physicalBlock h (sampleDummy h s isRow) = .dummy := rfl

@[simp] theorem sampleMarker_rigid (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) :
    rigidPosition h (sampleMarker h s isRow level mode group) = true := rfl

@[simp] theorem sampleDummy_rigid (h : Nat) (s : ProtectionSample h) (isRow : Bool) :
    rigidPosition h (sampleDummy h s isRow) = true := rfl

theorem sampleMarker_rowSelected (h : Nat) (s : ProtectionSample h)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) :
    rowSelected h s (sampleMarker h s true level mode group) := rfl

theorem sampleMarker_colSelected (h : Nat) (s : ProtectionSample h)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) :
    colSelected h s (sampleMarker h s false level mode group) := rfl

theorem sampleDummy_rowSelected (h : Nat) (s : ProtectionSample h) :
    rowSelected h s (sampleDummy h s true) := rfl

theorem sampleDummy_colSelected (h : Nat) (s : ProtectionSample h) :
    colSelected h s (sampleDummy h s false) := rfl

theorem pathVariable_rowSelected (h : Nat) (s : ProtectionSample h)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    rowSelected h s (pathVariable h s true d hd minus) := by
  by_cases ht : d = h
  · simp [rowSelected, pathVariable, ht, leafPosition, physicalCoordinate, rigidPosition]
  · by_cases hz : d = 0
    · subst d
      simp [rowSelected, pathVariable, ht, physicalCoordinate, rigidPosition]
    · simp [rowSelected, pathVariable, ht, hz, physicalCoordinate, rigidPosition]

theorem pathVariable_colSelected (h : Nat) (s : ProtectionSample h)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    colSelected h s (pathVariable h s false d hd minus) := by
  by_cases ht : d = h
  · simp [colSelected, pathVariable, ht, leafPosition, physicalCoordinate, rigidPosition]
  · by_cases hz : d = 0
    · subst d
      simp [colSelected, pathVariable, ht, physicalCoordinate, rigidPosition]
    · simp [colSelected, pathVariable, ht, hz, physicalCoordinate, rigidPosition]

theorem pathVariable_root_rigid (h : Nat) (hh : 0 < h) (s : ProtectionSample h)
    (isRow minus : Bool) :
    rigidPosition h (pathVariable h s isRow 0 (by omega) minus) = true := by
  simp [pathVariable, rigidPosition, show 0 ≠ h by omega]

theorem pathVariable_step_orders (h : Nat) (s : ProtectionSample h) (d : Nat)
    (hd : d + 1 ≤ h) :
    physicalBefore h true
      (pathVariable h s true (d + 1) hd false)
      (pathVariable h s true d (by omega) false) ∧
    physicalBefore h true
      (pathVariable h s true d (by omega) true)
      (pathVariable h s true (d + 1) hd true) ∧
    physicalBefore h false
      (pathVariable h s false d (by omega) false)
      (pathVariable h s false (d + 1) hd false) ∧
    physicalBefore h false
      (pathVariable h s false (d + 1) hd true)
      (pathVariable h s false d (by omega) true) := by
  have hp : d ≠ h := by omega
  have hs : d + 1 ≠ d := by omega
  have hs' : d ≠ d + 1 := by omega
  have hlt : d < d + 1 := by omega
  have hnlt : ¬ d + 1 < d := by omega
  have hdiff : d + 1 - d = 1 := by omega
  have hn := pathNode_parent h s d hd
  refine ⟨Or.inr ?_, Or.inr ?_, Or.inr ?_, Or.inr ?_⟩
  all_goals
    simp [pathVariable_block, hostComesBefore, hostVariableBefore, pathSign,
      hp, hs, hs', hlt, hnlt, hdiff, hn, signCode]

theorem protected_marker_row_entry (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) (c : PhysicalPosition h)
    (hc : colSelected h s c) :
    matrix (sampleMarker h s true level mode group) c =
      hostValue h (.anchor (modeFromCode mode.val (level.val + 1)) (group.val + 1))
        (physicalBlock h c) := by
  exact clean (_, c) ⟨sampleMarker_rowSelected h s level mode group, hc, Or.inl rfl⟩

theorem protected_marker_col_entry (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) (r : PhysicalPosition h)
    (hr : rowSelected h s r) :
    matrix r (sampleMarker h s false level mode group) =
      hostValue h (physicalBlock h r)
        (.anchor (modeFromCode mode.val (level.val + 1)) (group.val + 1)) := by
  exact clean (r, _) ⟨hr, sampleMarker_colSelected h s level mode group, Or.inr rfl⟩

theorem protected_dummy_row_entry (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    matrix (sampleDummy h s true) (pathVariable h s false d hd minus) = true := by
  have he : matrix (sampleDummy h s true) (pathVariable h s false d hd minus) =
      physicalMatrix h false (sampleDummy h s true) (pathVariable h s false d hd minus) :=
    clean (_, _) ⟨sampleDummy_rowSelected h s,
      pathVariable_colSelected h s d hd minus, Or.inl rfl⟩
  rw [he]
  simp [physicalMatrix, concreteHost, hostValue]

theorem protected_dummy_col_entry (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    matrix (pathVariable h s true d hd minus) (sampleDummy h s false) = true := by
  have he : matrix (pathVariable h s true d hd minus) (sampleDummy h s false) =
      physicalMatrix h false (pathVariable h s true d hd minus) (sampleDummy h s false) :=
    clean (_, _) ⟨pathVariable_rowSelected h s d hd minus,
      sampleDummy_colSelected h s, Or.inr rfl⟩
  rw [he]
  simp [physicalMatrix, concreteHost, hostValue]

theorem protected_root_values (h : Nat) (hh : 0 < h) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix) :
    matrix (pathVariable h s true 0 (by omega) false)
      (pathVariable h s false 0 (by omega) false) = true ∧
    matrix (pathVariable h s true 0 (by omega) true)
      (pathVariable h s false 0 (by omega) true) = false := by
  have he (minus : Bool) : matrix (pathVariable h s true 0 (by omega) minus)
      (pathVariable h s false 0 (by omega) minus) =
      physicalMatrix h false (pathVariable h s true 0 (by omega) minus)
        (pathVariable h s false 0 (by omega) minus) :=
    clean (pathVariable h s true 0 (by omega) minus, pathVariable h s false 0 (by omega) minus)
      ⟨pathVariable_rowSelected h s 0 (by omega) minus,
        pathVariable_colSelected h s 0 (by omega) minus,
        Or.inl (pathVariable_root_rigid h hh s true minus)⟩
  constructor
  · rw [he false]
    simp [physicalMatrix, concreteHost, hostValue, pathNode_zero, pathSign,
      show 0 ≠ h by omega]
  · rw [he true]
    simp [physicalMatrix, concreteHost, hostValue, pathNode_zero, pathSign,
      show 0 ≠ h by omega, hh]

end H4Formal
