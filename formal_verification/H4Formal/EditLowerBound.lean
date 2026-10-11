import H4Formal.SelectedPhysicalPath

namespace H4Formal

def pathVariable (h i a b own : Nat) (ha : a < 2 ^ h) (hb : b < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) : PhysicalPosition h :=
  selectedVariable h (min i h) a b own (Nat.min_le_right _ _) ha hb s hs

def pathLevel (h i : Nat) : Nat := min (max i 1) h

theorem pathLevel_valid (h i : Nat) (hh : 1 ≤ h) : 1 ≤ pathLevel h i ∧ pathLevel h i ≤ h := by
  simp only [pathLevel]
  omega

theorem pathLevel_eq (h i : Nat) (hi : 1 ≤ i) (hih : i ≤ h) : pathLevel h i = i := by
  simp [pathLevel, Nat.max_eq_left hi, Nat.min_eq_left hih]

def pathVAnchor (h i a b own : Nat) (hh : 1 ≤ h) (ho : own < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) (g : Fin 2) : PhysicalPosition h :=
  selectedAnchor h a b own ho (vMode (pathLevel h i) s)
    (vMode_valid h _ (pathLevel_valid h i hh).1 (pathLevel_valid h i hh).2 s hs)
    (g.val + 1) (by omega)

def pathWAnchor (h i a b own : Nat) (hh : 1 ≤ h) (ho : own < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) (g : Fin 2) : PhysicalPosition h :=
  selectedAnchor h a b own ho (wMode (pathLevel h i) (sampleNode h (pathLevel h i) a b) s)
    (wMode_valid h _ _ (pathLevel_valid h i hh).1 (pathLevel_valid h i hh).2 s hs)
    (g.val + 1) (by omega)

theorem pathVariable_selected (h i a b own : Nat) (ha : a < 2 ^ h) (hb : b < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) :
    SelectedPosition h a b own (pathVariable h i a b own ha hb s hs) := ⟨rfl, rfl⟩

theorem pathVAnchor_selected (h i a b own : Nat) (hh : 1 ≤ h) (ho : own < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) (g : Fin 2) :
    SelectedPosition h a b own (pathVAnchor h i a b own hh ho s hs g) := rfl

theorem pathWAnchor_selected (h i a b own : Nat) (hh : 1 ≤ h) (ho : own < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) (g : Fin 2) :
    SelectedPosition h a b own (pathWAnchor h i a b own hh ho s hs g) := rfl

theorem pathVAnchor_nonvariable (h i a b own : Nat) (hh : 1 ≤ h) (ho : own < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) (g : Fin 2) :
    NonVariable (pathVAnchor h i a b own hh ho s hs g).block := True.intro

theorem pathWAnchor_nonvariable (h i a b own : Nat) (hh : 1 ≤ h) (ho : own < 2 ^ h)
    (s : Sign) (hs : s = .plus ∨ s = .minus) (g : Fin 2) :
    NonVariable (pathWAnchor h i a b own hh ho s hs g).block := True.intro

theorem selected_four (h a b own : Nat) (x y z t : PhysicalPosition h)
    (hx : SelectedPosition h a b own x) (hy : SelectedPosition h a b own y)
    (hz : SelectedPosition h a b own z) (ht : SelectedPosition h a b own t) :
    ∀ p ∈ [x, y, z, t], SelectedPosition h a b own p := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> assumption

def selectionProtectedPath (h a b : Nat) (hh : 1 ≤ h) (ha : a < 2 ^ h) (hb : b < 2 ^ h)
    (D : PhysicalPosition h → PhysicalPosition h → Bool)
    (unchanged : ∀ r c, ProtectedCell h a b r c → D r c = hostValue h r.block c.block) :
    ProtectedPath (editedHost h D) h where
  plusRow i := pathVariable h i a b a ha hb .plus (Or.inl rfl)
  minusRow i := pathVariable h i a b a ha hb .minus (Or.inr rfl)
  plusCol i := pathVariable h i a b b ha hb .plus (Or.inl rfl)
  minusCol i := pathVariable h i a b b ha hb .minus (Or.inr rfl)
  dummyRow := selectedDummy h a ha
  dummyCol := selectedDummy h b hb
  vPlusRow i := pathVAnchor h i a b a hh ha .plus (Or.inl rfl)
  vMinusRow i := pathVAnchor h i a b a hh ha .minus (Or.inr rfl)
  wPlusRow i := pathWAnchor h i a b a hh ha .plus (Or.inl rfl)
  wMinusRow i := pathWAnchor h i a b a hh ha .minus (Or.inr rfl)
  vPlusCol i := pathVAnchor h i a b b hh hb .plus (Or.inl rfl)
  vMinusCol i := pathVAnchor h i a b b hh hb .minus (Or.inr rfl)
  wPlusCol i := pathWAnchor h i a b b hh hb .plus (Or.inl rfl)
  wMinusCol i := pathWAnchor h i a b b hh hb .minus (Or.inr rfl)
  vPlus := by
    intro i hi hih
    apply protected_frame_survives h a b D unchanged
    · exact selected_four _ _ _ _ _ _ _ _ (pathVAnchor_selected ..) (pathVAnchor_selected ..)
        (pathVariable_selected ..) (pathVariable_selected ..)
    · exact selected_four _ _ _ _ _ _ _ _ (pathVAnchor_selected ..) (pathVAnchor_selected ..)
        (selectedDummy_selected ..) (pathVariable_selected ..)
    · exact pathVAnchor_nonvariable ..
    · exact pathVAnchor_nonvariable ..
    · exact pathVAnchor_nonvariable ..
    · exact pathVAnchor_nonvariable ..
    · apply physical_frame_of_block_frame
      have hprev : i - 1 < h := by omega
      have hparent : sampleNode h i a b / 2 = sampleNode h (i - 1) a b :=
        sampleNode_parent h i a b hi hih
      have hs : levelSign h i .plus = .plus ∨ levelSign h i .plus = .leaf := by
        unfold levelSign; split <;> simp
      simpa [pathVAnchor, selectedAnchor, pathVariable, selectedVariable, selectedDummy,
        pathLevel_eq h i hi hih, Nat.min_eq_left hih, Nat.min_eq_left (by omega : i - 1 ≤ h),
        levelSign, Nat.ne_of_lt hprev, hparent] using
        vPlus_frame h i (sampleNode h i a b) hi (levelSign h i .plus) hs
  vMinus := by
    intro i hi hih
    apply protected_frame_survives h a b D unchanged
    · exact selected_four _ _ _ _ _ _ _ _ (pathVAnchor_selected ..) (pathVAnchor_selected ..)
        (pathVariable_selected ..) (pathVariable_selected ..)
    · exact selected_four _ _ _ _ _ _ _ _ (pathVAnchor_selected ..) (pathVAnchor_selected ..)
        (selectedDummy_selected ..) (pathVariable_selected ..)
    · exact pathVAnchor_nonvariable ..
    · exact pathVAnchor_nonvariable ..
    · exact pathVAnchor_nonvariable ..
    · exact pathVAnchor_nonvariable ..
    · apply physical_frame_of_block_frame
      have hprev : i - 1 < h := by omega
      have hparent := sampleNode_parent h i a b hi hih
      have hs : levelSign h i .minus = .minus ∨ levelSign h i .minus = .leaf := by
        unfold levelSign; split <;> simp
      simpa [pathVAnchor, selectedAnchor, pathVariable, selectedVariable, selectedDummy,
        pathLevel_eq h i hi hih, Nat.min_eq_left hih, Nat.min_eq_left (by omega : i - 1 ≤ h),
        levelSign, Nat.ne_of_lt hprev, hparent] using
        vMinus_frame h i (sampleNode h i a b) hi (levelSign h i .minus) hs
  wPlus := by
    intro i hi hih
    apply protected_frame_survives h a b D unchanged
    · exact selected_four _ _ _ _ _ _ _ _ (pathWAnchor_selected ..) (pathWAnchor_selected ..)
        (pathVariable_selected ..) (selectedDummy_selected ..)
    · exact selected_four _ _ _ _ _ _ _ _ (pathWAnchor_selected ..) (pathWAnchor_selected ..)
        (pathVariable_selected ..) (pathVariable_selected ..)
    · exact pathWAnchor_nonvariable ..
    · exact pathWAnchor_nonvariable ..
    · exact pathWAnchor_nonvariable ..
    · exact pathWAnchor_nonvariable ..
    · apply physical_frame_of_block_frame
      have hprev : i - 1 < h := by omega
      have hparent := sampleNode_parent h i a b hi hih
      have hs : levelSign h i .plus = .plus ∨ levelSign h i .plus = .leaf := by
        unfold levelSign; split <;> simp
      simpa [pathWAnchor, selectedAnchor, pathVariable, selectedVariable, selectedDummy,
        pathLevel_eq h i hi hih, Nat.min_eq_left hih, Nat.min_eq_left (by omega : i - 1 ≤ h),
        levelSign, Nat.ne_of_lt hprev, hparent] using
        wPlus_frame h i (sampleNode h i a b) hi (levelSign h i .plus) hs
  wMinus := by
    intro i hi hih
    apply protected_frame_survives h a b D unchanged
    · exact selected_four _ _ _ _ _ _ _ _ (pathWAnchor_selected ..) (pathWAnchor_selected ..)
        (pathVariable_selected ..) (selectedDummy_selected ..)
    · exact selected_four _ _ _ _ _ _ _ _ (pathWAnchor_selected ..) (pathWAnchor_selected ..)
        (pathVariable_selected ..) (pathVariable_selected ..)
    · exact pathWAnchor_nonvariable ..
    · exact pathWAnchor_nonvariable ..
    · exact pathWAnchor_nonvariable ..
    · exact pathWAnchor_nonvariable ..
    · apply physical_frame_of_block_frame
      have hprev : i - 1 < h := by omega
      have hparent := sampleNode_parent h i a b hi hih
      have hs : levelSign h i .minus = .minus ∨ levelSign h i .minus = .leaf := by
        unfold levelSign; split <;> simp
      simpa [pathWAnchor, selectedAnchor, pathVariable, selectedVariable, selectedDummy,
        pathLevel_eq h i hi hih, Nat.min_eq_left hih, Nat.min_eq_left (by omega : i - 1 ≤ h),
        levelSign, Nat.ne_of_lt hprev, hparent] using
        wMinus_frame h i (sampleNode h i a b) hi (levelSign h i .minus) hs
  dummyPlusRow := by
    intro i _
    rw [show (editedHost h D).value _ _ = D _ _ from rfl, unchanged]
    · rfl
    · exact ⟨pathVariable_selected .., selectedDummy_selected .., Or.inr (Or.inl True.intro)⟩
  dummyMinusRow := by
    intro i _
    rw [show (editedHost h D).value _ _ = D _ _ from rfl, unchanged]
    · rfl
    · exact ⟨pathVariable_selected .., selectedDummy_selected .., Or.inr (Or.inl True.intro)⟩
  dummyPlusCol := by
    intro i _
    rw [show (editedHost h D).value _ _ = D _ _ from rfl, unchanged]
    · rfl
    · exact ⟨selectedDummy_selected .., pathVariable_selected .., Or.inl True.intro⟩
  dummyMinusCol := by
    intro i _
    rw [show (editedHost h D).value _ _ = D _ _ from rfl, unchanged]
    · rfl
    · exact ⟨selectedDummy_selected .., pathVariable_selected .., Or.inl True.intro⟩
  rootPlus := by
    have hzero : 0 ≠ h := by omega
    rw [show (editedHost h D).value _ _ = D _ _ from rfl, unchanged]
    · simp [pathVariable, selectedVariable, levelSign, hzero, sampleNode_root h a b ha hb, hostValue]
    · refine ⟨pathVariable_selected .., pathVariable_selected .., Or.inr (Or.inr ?_)⟩
      simp [RootBlock, pathVariable, selectedVariable, levelSign, hzero, sampleNode_root h a b ha hb]
  rootMinus := by
    have hzero : 0 ≠ h := by omega
    rw [show (editedHost h D).value _ _ = D _ _ from rfl, unchanged]
    · simp [pathVariable, selectedVariable, levelSign, hzero, sampleNode_root h a b ha hb, hostValue]
    · refine ⟨pathVariable_selected .., pathVariable_selected .., Or.inr (Or.inr ?_)⟩
      simp [RootBlock, pathVariable, selectedVariable, levelSign, hzero, sampleNode_root h a b ha hb]
  leafRows := by simp [pathVariable, selectedVariable, levelSign]
  leafCols := by simp [pathVariable, selectedVariable, levelSign]

/-- Arbitrary two-way edit lower bound at every positive depth. -/
theorem arbitrary_edit_lower_bound (h : Nat) (hh : 1 ≤ h)
    (D : PhysicalPosition h → PhysicalPosition h → Bool)
    (edits : List (PhysicalPosition h × PhysicalPosition h))
    (covers : ∀ r c, D r c ≠ hostValue h r.block c.block → (r, c) ∈ edits)
    (hf : PatternFree (editedHost h D)) : 2 ^ h * 2 ^ h ≤ edits.length := by
  apply Classical.byContradiction
  intro hnot
  have hsmall : edits.length < 2 ^ h * 2 ^ h := by omega
  obtain ⟨a, b, ha, hb, havoid⟩ := exists_protected_selection h edits hsmall
  have unchanged : ∀ r c, ProtectedCell h a b r c → D r c = hostValue h r.block c.block := by
    intro r c hp
    by_cases he : D r c = hostValue h r.block c.block
    · exact he
    · exact False.elim (havoid (r, c) (covers r c he) hp)
  exact protected_path_not_free (editedHost h D) h (selectionProtectedPath h a b hh ha hb D unchanged) hf

end H4Formal
