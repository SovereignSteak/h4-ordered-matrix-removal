import H4Formal.ProtectedPath
import H4Formal.FourTuple

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def NonMarker : Block → Prop
  | .anchor _ _ => False
  | _ => True

theorem anchor_nonMarker_value (h : Nat) (m : Mode) (g : Nat) (b : Block)
    (hn : NonMarker b) :
    hostValue h (.anchor m g) b = decide (role b m .column = g) := by
  cases b <;> simp [NonMarker] at hn <;> rfl

theorem nonMarker_anchor_value (h : Nat) (m : Mode) (g : Nat) (b : Block)
    (hn : NonMarker b) :
    hostValue h b (.anchor m g) = decide (role b m .row = g) := by
  cases b <;> simp [NonMarker] at hn <;> rfl

theorem marker_before_nonMarker (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (level : Fin h) (mode : Fin 6) (group : Fin 2) (p : PhysicalPosition h)
    (hn : NonMarker (physicalBlock h p)) :
    physicalBefore h isRow (sampleMarker h s isRow level mode group) p := by
  apply Or.inr
  rw [sampleMarker_block]
  cases hb : physicalBlock h p <;> simp [hostComesBefore]
  simp [NonMarker, hb] at hn

theorem gadget_order (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (level : Fin h) (mode : Fin 6) (a b : PhysicalPosition h)
    (ha : NonMarker (physicalBlock h a)) (hb : NonMarker (physicalBlock h b))
    (hab : physicalBefore h isRow a b) :
    ∀ i j : Fin 4, i.val < j.val → physicalBefore h isRow
      (four (sampleMarker h s isRow level mode 0) (sampleMarker h s isRow level mode 1) a b i)
      (four (sampleMarker h s isRow level mode 0) (sampleMarker h s isRow level mode 1) a b j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> dsimp [four] at hij ⊢ <;> try omega
  all_goals first
    | exact hab
    | exact marker_before_nonMarker h s isRow level mode 0 a ha
    | exact marker_before_nonMarker h s isRow level mode 0 b hb
    | exact marker_before_nonMarker h s isRow level mode 1 a ha
    | exact marker_before_nonMarker h s isRow level mode 1 b hb
    | exact Or.inr (by simp [hostComesBefore, hostModeBefore])

theorem marker_pair_entry (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (level : Fin h) (mode : Fin 6) (g k : Fin 2) :
    matrix (sampleMarker h s true level mode g) (sampleMarker h s false level mode k) =
      decide (g.val ≠ k.val) := by
  rw [protected_marker_row_entry h s matrix clean level mode g _
    (sampleMarker_colSelected h s level mode k)]
  simp [hostValue]

theorem marker_row_body (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (level : Fin h) (mode : Fin 6) (g : Fin 2) (c : PhysicalPosition h)
    (hc : colSelected h s c) (hn : NonMarker (physicalBlock h c)) :
    matrix (sampleMarker h s true level mode g) c =
      decide (role (physicalBlock h c) (modeFromCode mode.val (level.val + 1)) .column = g.val + 1) := by
  rw [protected_marker_row_entry h s matrix clean level mode g c hc]
  exact anchor_nonMarker_value h _ _ _ hn

theorem marker_col_body (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (level : Fin h) (mode : Fin 6) (g : Fin 2) (r : PhysicalPosition h)
    (hr : rowSelected h s r) (hn : NonMarker (physicalBlock h r)) :
    matrix r (sampleMarker h s false level mode g) =
      decide (role (physicalBlock h r) (modeFromCode mode.val (level.val + 1)) .row = g.val + 1) := by
  rw [protected_marker_col_entry h s matrix clean level mode g r hr]
  exact nonMarker_anchor_value h _ _ _ hn

theorem protected_gadget_copy (h : Nat) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (level : Fin h) (mode : Fin 6) (r0 r1 c0 c1 : PhysicalPosition h)
    (sr0 : rowSelected h s r0) (sr1 : rowSelected h s r1)
    (sc0 : colSelected h s c0) (sc1 : colSelected h s c1)
    (nr0 : NonMarker (physicalBlock h r0)) (nr1 : NonMarker (physicalBlock h r1))
    (nc0 : NonMarker (physicalBlock h c0)) (nc1 : NonMarker (physicalBlock h c1))
    (orows : physicalBefore h true r0 r1) (ocols : physicalBefore h false c0 c1)
    (rr0 : role (physicalBlock h r0) (modeFromCode mode.val (level.val + 1)) .row = 1)
    (rr1 : role (physicalBlock h r1) (modeFromCode mode.val (level.val + 1)) .row = 2)
    (rc0 : role (physicalBlock h c0) (modeFromCode mode.val (level.val + 1)) .column = 1)
    (rc1 : role (physicalBlock h c1) (modeFromCode mode.val (level.val + 1)) .column = 2)
    (b00 : matrix r0 c0 = true) (b01 : matrix r0 c1 = false)
    (b10 : matrix r1 c0 = true) (b11 : matrix r1 c1 = true) :
    IsPhysicalCopy h matrix
      (four (sampleMarker h s true level mode 0) (sampleMarker h s true level mode 1) r0 r1)
      (four (sampleMarker h s false level mode 0) (sampleMarker h s false level mode 1) c0 c1) := by
  refine ⟨gadget_order h s true level mode r0 r1 nr0 nr1 orows,
    gadget_order h s false level mode c0 c1 nc0 nc1 ocols, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [four]
  · simpa [pattern] using marker_pair_entry h s matrix clean level mode 0 0
  · simpa [pattern] using marker_pair_entry h s matrix clean level mode 0 1
  · simpa [pattern, rc0] using marker_row_body h s matrix clean level mode 0 c0 sc0 nc0
  · simpa [pattern, rc1] using marker_row_body h s matrix clean level mode 0 c1 sc1 nc1
  · simpa [pattern] using marker_pair_entry h s matrix clean level mode 1 0
  · simpa [pattern] using marker_pair_entry h s matrix clean level mode 1 1
  · simpa [pattern, rc0] using marker_row_body h s matrix clean level mode 1 c0 sc0 nc0
  · simpa [pattern, rc1] using marker_row_body h s matrix clean level mode 1 c1 sc1 nc1
  · simpa [pattern, rr0] using marker_col_body h s matrix clean level mode 0 r0 sr0 nr0
  · simpa [pattern, rr0] using marker_col_body h s matrix clean level mode 1 r0 sr0 nr0
  · exact b00
  · exact b01
  · simpa [pattern, rr1] using marker_col_body h s matrix clean level mode 0 r1 sr1 nr1
  · simpa [pattern, rr1] using marker_col_body h s matrix clean level mode 1 r1 sr1 nr1
  · exact b10
  · exact b11


structure GadgetOrder (h : Nat) where
  before : Bool → PhysicalPosition h → PhysicalPosition h → Prop
  marker_group : ∀ s axis level mode,
    before axis (sampleMarker h s axis level mode 0) (sampleMarker h s axis level mode 1)
  marker_body : ∀ s axis level mode group p, NonMarker (physicalBlock h p) →
    before axis (sampleMarker h s axis level mode group) p
  body_order : ∀ axis a b, NonMarker (physicalBlock h a) → NonMarker (physicalBlock h b) →
    physicalBefore h axis a b → before axis a b

def IsOrderedPhysicalCopy (h : Nat) (order : GadgetOrder h) (matrix : PhysicalMatrix h)
    (rows cols : Fin 4 → PhysicalPosition h) : Prop :=
  (∀ i j, i.val < j.val → order.before true (rows i) (rows j)) ∧
  (∀ i j, i.val < j.val → order.before false (cols i) (cols j)) ∧
  (∀ i j, matrix (rows i) (cols j) = pattern i j)

def IsOrderedPhysicalFree (h : Nat) (order : GadgetOrder h) (matrix : PhysicalMatrix h) : Prop :=
  ∀ rows cols, ¬ IsOrderedPhysicalCopy h order matrix rows cols

def canonicalGadgetOrder (h : Nat) : GadgetOrder h where
  before := physicalBefore h
  marker_group := by
    intro s axis level mode
    exact Or.inr (by simp [hostComesBefore, hostModeBefore])
  marker_body := marker_before_nonMarker h
  body_order := fun _ _ _ _ _ ho => ho

theorem ordered_gadget_order (h : Nat) (order : GadgetOrder h)
    (s : ProtectionSample h) (axis : Bool) (level : Fin h) (mode : Fin 6)
    (a b : PhysicalPosition h) (ha : NonMarker (physicalBlock h a))
    (hb : NonMarker (physicalBlock h b)) (hab : physicalBefore h axis a b) :
    ∀ i j : Fin 4, i.val < j.val → order.before axis
      (four (sampleMarker h s axis level mode 0) (sampleMarker h s axis level mode 1) a b i)
      (four (sampleMarker h s axis level mode 0) (sampleMarker h s axis level mode 1) a b j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> dsimp [four] at hij ⊢ <;> try omega
  all_goals first
    | exact order.body_order axis a b ha hb hab
    | exact order.marker_body s axis level mode 0 a ha
    | exact order.marker_body s axis level mode 0 b hb
    | exact order.marker_body s axis level mode 1 a ha
    | exact order.marker_body s axis level mode 1 b hb
    | exact order.marker_group s axis level mode

theorem ordered_protected_gadget_copy (h : Nat) (order : GadgetOrder h)
    (s : ProtectionSample h) (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix)
    (level : Fin h) (mode : Fin 6) (r0 r1 c0 c1 : PhysicalPosition h)
    (sr0 : rowSelected h s r0) (sr1 : rowSelected h s r1)
    (sc0 : colSelected h s c0) (sc1 : colSelected h s c1)
    (nr0 : NonMarker (physicalBlock h r0)) (nr1 : NonMarker (physicalBlock h r1))
    (nc0 : NonMarker (physicalBlock h c0)) (nc1 : NonMarker (physicalBlock h c1))
    (orows : physicalBefore h true r0 r1) (ocols : physicalBefore h false c0 c1)
    (rr0 : role (physicalBlock h r0) (modeFromCode mode.val (level.val + 1)) .row = 1)
    (rr1 : role (physicalBlock h r1) (modeFromCode mode.val (level.val + 1)) .row = 2)
    (rc0 : role (physicalBlock h c0) (modeFromCode mode.val (level.val + 1)) .column = 1)
    (rc1 : role (physicalBlock h c1) (modeFromCode mode.val (level.val + 1)) .column = 2)
    (b00 : matrix r0 c0 = true) (b01 : matrix r0 c1 = false)
    (b10 : matrix r1 c0 = true) (b11 : matrix r1 c1 = true) :
    IsOrderedPhysicalCopy h order matrix
      (four (sampleMarker h s true level mode 0) (sampleMarker h s true level mode 1) r0 r1)
      (four (sampleMarker h s false level mode 0) (sampleMarker h s false level mode 1) c0 c1) := by
  exact ⟨ordered_gadget_order h order s true level mode r0 r1 nr0 nr1 orows,
    ordered_gadget_order h order s false level mode c0 c1 nc0 nc1 ocols,
    (protected_gadget_copy h s matrix clean level mode r0 r1 c0 c1 sr0 sr1 sc0 sc1
      nr0 nr1 nc0 nc1 orows ocols rr0 rr1 rc0 rc1 b00 b01 b10 b11).2.2⟩

end H4Formal
