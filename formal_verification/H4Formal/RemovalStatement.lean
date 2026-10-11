import H4Formal.RealAsymptotics

namespace H4Formal

def numericMatrix {n : Nat} (D : Fin n → Fin n → Bool) : OrderedMatrix (Fin n) (Fin n) where
  value := D
  rowBefore i j := i.val < j.val
  colBefore i j := i.val < j.val

def allFiniteFour (n : Nat) := listFour (List.finRange n) (List.finRange n)
  (List.finRange n) (List.finRange n)

theorem mem_allFiniteFour (n : Nat) (r : Fin 4 → Fin n) : r ∈ allFiniteFour n :=
  (mem_listFour ..).2 ⟨finRange_mem _ _, finRange_mem _ _, finRange_mem _ _, finRange_mem _ _⟩

theorem allFiniteFour_nodup (n : Nat) : (allFiniteFour n).Nodup :=
  listFour_nodup _ _ _ _ (finRange_nodup _) (finRange_nodup _) (finRange_nodup _) (finRange_nodup _)

noncomputable def matrixCopyEnumeration {n : Nat} (A : OrderedMatrix (Fin n) (Fin n)) := by
  classical
  exact (listProduct (allFiniteFour n) (allFiniteFour n)).filter
    (fun x => decide (MatrixCopy A x.1 x.2))

theorem mem_matrixCopyEnumeration {n : Nat} (A : OrderedMatrix (Fin n) (Fin n))
    (r c : Fin 4 → Fin n) : (r, c) ∈ matrixCopyEnumeration A ↔ MatrixCopy A r c := by
  classical
  simp [matrixCopyEnumeration, mem_listProduct, mem_allFiniteFour]

theorem matrixCopyEnumeration_nodup {n : Nat} (A : OrderedMatrix (Fin n) (Fin n)) :
    (matrixCopyEnumeration A).Nodup := by
  classical
  exact (listProduct_nodup _ _ (allFiniteFour_nodup _) (allFiniteFour_nodup _)).filter _

/-- Each pair of increasing four-tuples is counted once. -/
noncomputable def matrixCopyCount {n : Nat} (A : OrderedMatrix (Fin n) (Fin n)) : Nat :=
  (matrixCopyEnumeration A).length

theorem matrixCopyCount_standardHost (h : Nat) :
    matrixCopyCount (standardHost h) = hostCopyCount h := by
  unfold matrixCopyCount hostCopyCount
  apply nodup_same_members_length _ _ (matrixCopyEnumeration_nodup _)
    (standardCopyEnumeration_nodup _ _)
  rintro ⟨r, c⟩
  rw [mem_matrixCopyEnumeration, mem_standardCopyEnumeration]

theorem numericMatrix_standardHost (h : Nat) (repair : Bool) :
    numericMatrix (standardHost h repair).value = standardHost h repair := rfl

/-- A polynomial lower bound for every ordinary ordered Boolean matrix. -/
noncomputable def PolynomialRemovalBound (c C : ℝ) : Prop :=
  ∀ (n : Nat) (D : Fin n → Fin n → Bool) (ε : ℝ),
    1 ≤ n → 0 < ε → ε ≤ 1 →
    ε ≤ (editDistance (numericMatrix D) : ℝ) / (n : ℝ) ^ 2 →
    c * ε ^ C ≤ (matrixCopyCount (numericMatrix D) : ℝ) / (n : ℝ) ^ 8

end H4Formal
