import H4Formal.CopyGadgets

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

theorem pathVariable_nonMarker (h : Nat) (s : ProtectionSample h) (isRow : Bool)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    NonMarker (physicalBlock h (pathVariable h s isRow d hd minus)) := by
  rw [pathVariable_block]
  trivial

theorem sampleDummy_nonMarker (h : Nat) (s : ProtectionSample h) (isRow : Bool) :
    NonMarker (physicalBlock h (sampleDummy h s isRow)) := by
  rw [sampleDummy_block]
  trivial

theorem pathVariable_before_rowDummy (h : Nat) (s : ProtectionSample h)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    physicalBefore h true (pathVariable h s true d hd minus) (sampleDummy h s true) := by
  exact Or.inr (by simp [hostComesBefore])

theorem colDummy_before_pathVariable (h : Nat) (s : ProtectionSample h)
    (d : Nat) (hd : d ≤ h) (minus : Bool) :
    physicalBefore h false (sampleDummy h s false) (pathVariable h s false d hd minus) := by
  exact Or.inr (by simp [hostComesBefore])

theorem forcing_step_for_order (h : Nat) (order : GadgetOrder h) (s : ProtectionSample h) (matrix : PhysicalMatrix h)
    (clean : ProtectedClean h s matrix) (free : IsOrderedPhysicalFree h order matrix) (d : Fin h)
    (previousPlus : matrix (pathVariable h s true d.val (by omega) false)
      (pathVariable h s false d.val (by omega) false) = true)
    (previousMinus : matrix (pathVariable h s true d.val (by omega) true)
      (pathVariable h s false d.val (by omega) true) = false) :
    matrix (pathVariable h s true (d.val + 1) (by omega) false)
      (pathVariable h s false (d.val + 1) (by omega) false) = true ∧
    matrix (pathVariable h s true (d.val + 1) (by omega) true)
      (pathVariable h s false (d.val + 1) (by omega) true) = false := by
  have hd := d.isLt
  have hp : d.val ≠ h := by omega
  have hs : d.val ≠ d.val + 1 := by omega
  have hs' : d.val + 1 ≠ d.val := by omega
  let xp0 := pathVariable h s true d.val (by omega) false
  let xm0 := pathVariable h s true d.val (by omega) true
  let yp0 := pathVariable h s false d.val (by omega) false
  let ym0 := pathVariable h s false d.val (by omega) true
  let xp1 := pathVariable h s true (d.val + 1) (by omega) false
  let xm1 := pathVariable h s true (d.val + 1) (by omega) true
  let yp1 := pathVariable h s false (d.val + 1) (by omega) false
  let ym1 := pathVariable h s false (d.val + 1) (by omega) true
  let parity := pathNode h s (d.val + 1) % 2
  have hpar : parity < 2 := Nat.mod_lt _ (by decide)
  have hpcases : parity = 0 ∨ parity = 1 := by omega
  let wp : Fin 6 := ⟨2 + parity, by omega⟩
  let wm : Fin 6 := ⟨4 + parity, by omega⟩
  have ord := pathVariable_step_orders h s d.val (by omega)
  have vplusRoles :
      role (physicalBlock h xp1) (modeFromCode 0 (d.val + 1)) .row = 1 ∧
      role (physicalBlock h xp0) (modeFromCode 0 (d.val + 1)) .row = 2 ∧
      role .dummy (modeFromCode 0 (d.val + 1)) .column = 1 ∧
      role (physicalBlock h yp0) (modeFromCode 0 (d.val + 1)) .column = 2 := by
    by_cases ht : d.val + 1 = h <;>
      simp [xp1, xp0, yp0, role, modeFromCode, matchesBlock, pathSign, hp, ht, hs, hs']
    all_goals omega
  have vminusRoles :
      role (physicalBlock h xm0) (modeFromCode 1 (d.val + 1)) .row = 1 ∧
      role (physicalBlock h xm1) (modeFromCode 1 (d.val + 1)) .row = 2 ∧
      role .dummy (modeFromCode 1 (d.val + 1)) .column = 1 ∧
      role (physicalBlock h ym0) (modeFromCode 1 (d.val + 1)) .column = 2 := by
    by_cases ht : d.val + 1 = h <;>
      simp [xm0, xm1, ym0, role, modeFromCode, matchesBlock, pathSign, hp, ht, hs, hs']
    all_goals omega
  have wplusRoles :
      role (physicalBlock h xp1) (modeFromCode wp.val (d.val + 1)) .row = 1 ∧
      role .dummy (modeFromCode wp.val (d.val + 1)) .row = 2 ∧
      role (physicalBlock h yp0) (modeFromCode wp.val (d.val + 1)) .column = 1 ∧
      role (physicalBlock h yp1) (modeFromCode wp.val (d.val + 1)) .column = 2 := by
    rcases hpcases with he | he <;> by_cases ht : d.val + 1 = h
    all_goals
      have hbit : pathNode h s (d.val + 1) % 2 = parity := rfl
      simp only [ht] at hbit
      simp [xp1, yp0, yp1, wp, role, modeFromCode, matchesBlock, pathSign,
        hp, ht, hs, hs', he, hbit]
    all_goals omega
  have wminusRoles :
      role (physicalBlock h xm1) (modeFromCode wm.val (d.val + 1)) .row = 1 ∧
      role .dummy (modeFromCode wm.val (d.val + 1)) .row = 2 ∧
      role (physicalBlock h ym1) (modeFromCode wm.val (d.val + 1)) .column = 1 ∧
      role (physicalBlock h ym0) (modeFromCode wm.val (d.val + 1)) .column = 2 := by
    rcases hpcases with he | he <;> by_cases ht : d.val + 1 = h
    all_goals
      have hbit : pathNode h s (d.val + 1) % 2 = parity := rfl
      simp only [ht] at hbit
      simp [xm1, ym1, ym0, wm, role, modeFromCode, matchesBlock, pathSign,
        hp, ht, hs, hs', he, hbit]
    all_goals omega
  have plusCross : matrix xp1 yp0 = true := by
    cases he : matrix xp1 yp0 with
    | false =>
        exfalso
        apply free
          (four (sampleMarker h s true d 0 0) (sampleMarker h s true d 0 1) xp1 xp0)
          (four (sampleMarker h s false d 0 0) (sampleMarker h s false d 0 1)
            (sampleDummy h s false) yp0)
        exact ordered_protected_gadget_copy h order s matrix clean d 0 xp1 xp0 (sampleDummy h s false) yp0
          (pathVariable_rowSelected h s _ _ _) (pathVariable_rowSelected h s _ _ _)
          (sampleDummy_colSelected h s) (pathVariable_colSelected h s _ _ _)
          (pathVariable_nonMarker h s _ _ _ _) (pathVariable_nonMarker h s _ _ _ _)
          (sampleDummy_nonMarker h s false) (pathVariable_nonMarker h s _ _ _ _)
          ord.1 (colDummy_before_pathVariable h s _ _ _)
          vplusRoles.1 vplusRoles.2.1 vplusRoles.2.2.1 vplusRoles.2.2.2
          (protected_dummy_col_entry h s matrix clean _ _ _) he
          (protected_dummy_col_entry h s matrix clean _ _ _) previousPlus
    | true => rfl
  have minusCross : matrix xm1 ym0 = false := by
    cases he : matrix xm1 ym0 with
    | false => rfl
    | true =>
        exfalso
        apply free
          (four (sampleMarker h s true d 1 0) (sampleMarker h s true d 1 1) xm0 xm1)
          (four (sampleMarker h s false d 1 0) (sampleMarker h s false d 1 1)
            (sampleDummy h s false) ym0)
        exact ordered_protected_gadget_copy h order s matrix clean d 1 xm0 xm1 (sampleDummy h s false) ym0
          (pathVariable_rowSelected h s _ _ _) (pathVariable_rowSelected h s _ _ _)
          (sampleDummy_colSelected h s) (pathVariable_colSelected h s _ _ _)
          (pathVariable_nonMarker h s _ _ _ _) (pathVariable_nonMarker h s _ _ _ _)
          (sampleDummy_nonMarker h s false) (pathVariable_nonMarker h s _ _ _ _)
          ord.2.1 (colDummy_before_pathVariable h s _ _ _)
          vminusRoles.1 vminusRoles.2.1 vminusRoles.2.2.1 vminusRoles.2.2.2
          (protected_dummy_col_entry h s matrix clean _ _ _) previousMinus
          (protected_dummy_col_entry h s matrix clean _ _ _) he
  constructor
  · change matrix xp1 yp1 = true
    cases he : matrix xp1 yp1 with
    | false =>
        exfalso
        apply free
          (four (sampleMarker h s true d wp 0) (sampleMarker h s true d wp 1)
            xp1 (sampleDummy h s true))
          (four (sampleMarker h s false d wp 0) (sampleMarker h s false d wp 1) yp0 yp1)
        exact ordered_protected_gadget_copy h order s matrix clean d wp xp1 (sampleDummy h s true) yp0 yp1
          (pathVariable_rowSelected h s _ _ _) (sampleDummy_rowSelected h s)
          (pathVariable_colSelected h s _ _ _) (pathVariable_colSelected h s _ _ _)
          (pathVariable_nonMarker h s _ _ _ _) (sampleDummy_nonMarker h s true)
          (pathVariable_nonMarker h s _ _ _ _) (pathVariable_nonMarker h s _ _ _ _)
          (pathVariable_before_rowDummy h s _ _ _) ord.2.2.1
          wplusRoles.1 wplusRoles.2.1 wplusRoles.2.2.1 wplusRoles.2.2.2
          plusCross he (protected_dummy_row_entry h s matrix clean _ _ _)
          (protected_dummy_row_entry h s matrix clean _ _ _)
    | true => rfl
  · change matrix xm1 ym1 = false
    cases he : matrix xm1 ym1 with
    | false => rfl
    | true =>
        exfalso
        apply free
          (four (sampleMarker h s true d wm 0) (sampleMarker h s true d wm 1)
            xm1 (sampleDummy h s true))
          (four (sampleMarker h s false d wm 0) (sampleMarker h s false d wm 1) ym1 ym0)
        exact ordered_protected_gadget_copy h order s matrix clean d wm xm1 (sampleDummy h s true) ym1 ym0
          (pathVariable_rowSelected h s _ _ _) (sampleDummy_rowSelected h s)
          (pathVariable_colSelected h s _ _ _) (pathVariable_colSelected h s _ _ _)
          (pathVariable_nonMarker h s _ _ _ _) (sampleDummy_nonMarker h s true)
          (pathVariable_nonMarker h s _ _ _ _) (pathVariable_nonMarker h s _ _ _ _)
          (pathVariable_before_rowDummy h s _ _ _) ord.2.2.2
          wminusRoles.1 wminusRoles.2.1 wminusRoles.2.2.1 wminusRoles.2.2.2
          he minusCross (protected_dummy_row_entry h s matrix clean _ _ _)
          (protected_dummy_row_entry h s matrix clean _ _ _)

theorem clean_sample_not_free_for_order (h : Nat) (order : GadgetOrder h) (hh : 0 < h) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix) :
    ¬ IsOrderedPhysicalFree h order matrix := by
  intro free
  have values (d : Nat) : ∀ hd : d ≤ h,
      matrix (pathVariable h s true d hd false) (pathVariable h s false d hd false) = true ∧
      matrix (pathVariable h s true d hd true) (pathVariable h s false d hd true) = false := by
    induction d with
    | zero =>
        intro hd
        exact protected_root_values h hh s matrix clean
    | succ d ih =>
        intro hd
        exact forcing_step_for_order h order s matrix clean free ⟨d, by omega⟩
          (ih (by omega)).1 (ih (by omega)).2
  have last := values h (Nat.le_refl h)
  have hp : matrix (leafPosition h (sampleLeaf h s)) (leafPosition h (sampleLeaf h s)) = true := by
    simpa [pathVariable] using last.1
  have hm : matrix (leafPosition h (sampleLeaf h s)) (leafPosition h (sampleLeaf h s)) = false := by
    simpa [pathVariable] using last.2
  rw [hp] at hm
  cases hm

theorem forcing_step (h : Nat) (s : ProtectionSample h) (matrix : PhysicalMatrix h)
    (clean : ProtectedClean h s matrix) (free : IsPhysicalFree h matrix) (d : Fin h)
    (previousPlus : matrix (pathVariable h s true d.val (by omega) false)
      (pathVariable h s false d.val (by omega) false) = true)
    (previousMinus : matrix (pathVariable h s true d.val (by omega) true)
      (pathVariable h s false d.val (by omega) true) = false) :
    matrix (pathVariable h s true (d.val + 1) (by omega) false)
      (pathVariable h s false (d.val + 1) (by omega) false) = true ∧
    matrix (pathVariable h s true (d.val + 1) (by omega) true)
      (pathVariable h s false (d.val + 1) (by omega) true) = false :=
  forcing_step_for_order h (canonicalGadgetOrder h) s matrix clean free d previousPlus previousMinus

theorem clean_sample_not_free (h : Nat) (hh : 0 < h) (s : ProtectionSample h)
    (matrix : PhysicalMatrix h) (clean : ProtectedClean h s matrix) :
    ¬ IsPhysicalFree h matrix :=
  clean_sample_not_free_for_order h (canonicalGadgetOrder h) hh s matrix clean

theorem ordered_arbitrary_edit_lower_bound (h : Nat) (order : GadgetOrder h)
    (hh : 0 < h) (matrix : PhysicalMatrix h) (free : IsOrderedPhysicalFree h order matrix) :
    (2 ^ h) ^ 2 ≤ editCount h (physicalMatrix h false) matrix := by
  by_contra hn
  have he : editCount h (physicalMatrix h false) matrix < (2 ^ h) ^ 2 := by omega
  obtain ⟨s, clean⟩ := exists_protected_clean_sample h matrix he
  exact clean_sample_not_free_for_order h order hh s matrix clean free

theorem arbitrary_edit_lower_bound (h : Nat) (hh : 0 < h) (matrix : PhysicalMatrix h)
    (free : IsPhysicalFree h matrix) :
    (2 ^ h) ^ 2 ≤ editCount h (physicalMatrix h false) matrix := by
  by_contra hn
  have he : editCount h (physicalMatrix h false) matrix < (2 ^ h) ^ 2 := by omega
  obtain ⟨s, clean⟩ := exists_protected_clean_sample h matrix he
  exact clean_sample_not_free h hh s matrix clean free

end H4Formal
