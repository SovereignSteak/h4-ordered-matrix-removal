import H4Formal.Matrix

namespace H4Formal

/-- Ordered marker/signature frame, with the four variable body cells omitted. -/
structure MarkerFrame {R C : Type} (M : OrderedMatrix R C)
    (r0 r1 x y : R) (c0 c1 u v : C) : Prop where
  rows : IncreasingFour M.rowBefore r0 r1 x y
  cols : IncreasingFour M.colBefore c0 c1 u v
  a00 : M.value r0 c0 = false
  a01 : M.value r0 c1 = true
  a10 : M.value r1 c0 = true
  a11 : M.value r1 c1 = false
  a02 : M.value r0 u = true
  a03 : M.value r0 v = false
  a12 : M.value r1 u = false
  a13 : M.value r1 v = true
  a20 : M.value x c0 = true
  a21 : M.value x c1 = false
  a30 : M.value y c0 = false
  a31 : M.value y c1 = true

theorem frame_completes_copy {R C : Type} (M : OrderedMatrix R C)
    (r0 r1 x y : R) (c0 c1 u v : C)
    (f : MarkerFrame M r0 r1 x y c0 c1 u v)
    (h22 : M.value x u = true) (h23 : M.value x v = false)
    (h32 : M.value y u = true) (h33 : M.value y v = true) :
    MatrixCopy M (four r0 r1 x y) (four c0 c1 u v) := by
  apply (matrixCopy_four_iff M r0 r1 x y c0 c1 u v).2
  exact ⟨f.rows, f.cols, f.a00, f.a01, f.a02, f.a03,
    f.a10, f.a11, f.a12, f.a13, f.a20, f.a21, h22, h23, f.a30, f.a31, h32, h33⟩

theorem frame_forces_top_right {R C : Type} (M : OrderedMatrix R C)
    (hf : PatternFree M) (r0 r1 x y : R) (c0 c1 u v : C)
    (f : MarkerFrame M r0 r1 x y c0 c1 u v)
    (h22 : M.value x u = true) (h32 : M.value y u = true)
    (h33 : M.value y v = true) : M.value x v = true := by
  cases h : M.value x v
  · exact False.elim (hf _ _ (frame_completes_copy M r0 r1 x y c0 c1 u v f h22 h h32 h33))
  · rfl

theorem frame_forces_bottom_right {R C : Type} (M : OrderedMatrix R C)
    (hf : PatternFree M) (r0 r1 x y : R) (c0 c1 u v : C)
    (f : MarkerFrame M r0 r1 x y c0 c1 u v)
    (h22 : M.value x u = true) (h23 : M.value x v = false)
    (h32 : M.value y u = true) : M.value y v = false := by
  cases h : M.value y v
  · rfl
  · exact False.elim (hf _ _ (frame_completes_copy M r0 r1 x y c0 c1 u v f h22 h23 h32 h))

theorem frame_forces_top_left {R C : Type} (M : OrderedMatrix R C)
    (hf : PatternFree M) (r0 r1 x y : R) (c0 c1 u v : C)
    (f : MarkerFrame M r0 r1 x y c0 c1 u v)
    (h23 : M.value x v = false) (h32 : M.value y u = true)
    (h33 : M.value y v = true) : M.value x u = false := by
  cases h : M.value x u
  · rfl
  · exact False.elim (hf _ _ (frame_completes_copy M r0 r1 x y c0 c1 u v f h h23 h32 h33))

/-- All protected entries for one selected root-to-leaf path. -/
structure ProtectedPath {R C : Type} (M : OrderedMatrix R C) (h : Nat) where
  plusRow : Nat → R
  minusRow : Nat → R
  plusCol : Nat → C
  minusCol : Nat → C
  dummyRow : R
  dummyCol : C
  vPlusRow : Nat → Fin 2 → R
  vMinusRow : Nat → Fin 2 → R
  wPlusRow : Nat → Fin 2 → R
  wMinusRow : Nat → Fin 2 → R
  vPlusCol : Nat → Fin 2 → C
  vMinusCol : Nat → Fin 2 → C
  wPlusCol : Nat → Fin 2 → C
  wMinusCol : Nat → Fin 2 → C
  vPlus : ∀ i, 1 ≤ i → i ≤ h →
    MarkerFrame M (vPlusRow i 0) (vPlusRow i 1) (plusRow i) (plusRow (i - 1))
      (vPlusCol i 0) (vPlusCol i 1) dummyCol (plusCol (i - 1))
  vMinus : ∀ i, 1 ≤ i → i ≤ h →
    MarkerFrame M (vMinusRow i 0) (vMinusRow i 1) (minusRow (i - 1)) (minusRow i)
      (vMinusCol i 0) (vMinusCol i 1) dummyCol (minusCol (i - 1))
  wPlus : ∀ i, 1 ≤ i → i ≤ h →
    MarkerFrame M (wPlusRow i 0) (wPlusRow i 1) (plusRow i) dummyRow
      (wPlusCol i 0) (wPlusCol i 1) (plusCol (i - 1)) (plusCol i)
  wMinus : ∀ i, 1 ≤ i → i ≤ h →
    MarkerFrame M (wMinusRow i 0) (wMinusRow i 1) (minusRow i) dummyRow
      (wMinusCol i 0) (wMinusCol i 1) (minusCol i) (minusCol (i - 1))
  dummyPlusRow : ∀ i, i ≤ h → M.value (plusRow i) dummyCol = true
  dummyMinusRow : ∀ i, i ≤ h → M.value (minusRow i) dummyCol = true
  dummyPlusCol : ∀ i, i ≤ h → M.value dummyRow (plusCol i) = true
  dummyMinusCol : ∀ i, i ≤ h → M.value dummyRow (minusCol i) = true
  rootPlus : M.value (plusRow 0) (plusCol 0) = true
  rootMinus : M.value (minusRow 0) (minusCol 0) = false
  leafRows : plusRow h = minusRow h
  leafCols : plusCol h = minusCol h

theorem protected_path_forces_diagonals {R C : Type} (M : OrderedMatrix R C)
    (h : Nat) (p : ProtectedPath M h) (hf : PatternFree M) :
    ∀ i, i ≤ h →
      M.value (p.plusRow i) (p.plusCol i) = true ∧
      M.value (p.minusRow i) (p.minusCol i) = false := by
  intro i
  induction i with
  | zero => intro _; exact ⟨p.rootPlus, p.rootMinus⟩
  | succ i ih =>
      intro hih
      have hi : i ≤ h := by omega
      have hp := ih hi
      have positive : 1 ≤ i + 1 := by omega
      have crossPlus : M.value (p.plusRow (i + 1)) (p.plusCol i) = true := by
        exact frame_forces_top_right M hf _ _ _ _ _ _ _ _
          (p.vPlus (i + 1) positive hih) (p.dummyPlusRow _ hih)
          (p.dummyPlusRow _ hi) (by simpa using hp.1)
      have crossMinus : M.value (p.minusRow (i + 1)) (p.minusCol i) = false := by
        exact frame_forces_bottom_right M hf _ _ _ _ _ _ _ _
          (p.vMinus (i + 1) positive hih) (p.dummyMinusRow _ hi)
          (by simpa using hp.2) (p.dummyMinusRow _ hih)
      constructor
      · exact frame_forces_top_right M hf _ _ _ _ _ _ _ _
          (p.wPlus (i + 1) positive hih) (by simpa using crossPlus)
          (p.dummyPlusCol _ hi) (p.dummyPlusCol _ hih)
      · exact frame_forces_top_left M hf _ _ _ _ _ _ _ _
          (p.wMinus (i + 1) positive hih) (by simpa using crossMinus)
          (p.dummyMinusCol _ hih) (p.dummyMinusCol _ hi)

theorem protected_path_not_free {R C : Type} (M : OrderedMatrix R C)
    (h : Nat) (p : ProtectedPath M h) : ¬ PatternFree M := by
  intro hf
  have forced := protected_path_forces_diagonals M h p hf h (Nat.le_refl h)
  have heq : M.value (p.plusRow h) (p.plusCol h) =
      M.value (p.minusRow h) (p.minusCol h) := by rw [p.leafRows, p.leafCols]
  have impossible : true = false := forced.1.symm.trans (heq.trans forced.2)
  cases impossible

end H4Formal
