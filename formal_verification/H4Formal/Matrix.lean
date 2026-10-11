import H4Formal.Pattern

namespace H4Formal

@[simp] theorem forall_fin_zero (P : Fin 0 → Prop) : (∀ i, P i) ↔ True :=
  ⟨fun _ => True.intro, fun _ i => Fin.elim0 i⟩

structure OrderedMatrix (R C : Type) where
  value : R → C → Bool
  rowBefore : R → R → Prop
  colBefore : C → C → Prop

def four {α : Type} (a b c d : α) (i : Fin 4) : α :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

def IncreasingFour {α : Type} (lt : α → α → Prop) (a b c d : α) : Prop :=
  lt a b ∧ lt a c ∧ lt a d ∧ lt b c ∧ lt b d ∧ lt c d

def MatrixCopy {R C : Type} (M : OrderedMatrix R C)
    (r : Fin 4 → R) (c : Fin 4 → C) : Prop :=
  (∀ i j, i.val < j.val → M.rowBefore (r i) (r j)) ∧
  (∀ i j, i.val < j.val → M.colBefore (c i) (c j)) ∧
  (∀ i j, M.value (r i) (c j) = pattern i j)

def PatternFree {R C : Type} (M : OrderedMatrix R C) : Prop :=
  ∀ r c, ¬ MatrixCopy M r c

theorem four_increasing_iff {α : Type} (lt : α → α → Prop) (a b c d : α) :
    (∀ i j : Fin 4, i.val < j.val → lt (four a b c d i) (four a b c d j)) ↔
      IncreasingFour lt a b c d := by
  simp [Fin.forall_fin_succ, four, IncreasingFour, and_assoc]

theorem matrixCopy_four_iff {R C : Type} (M : OrderedMatrix R C)
    (r0 r1 r2 r3 : R) (c0 c1 c2 c3 : C) :
    MatrixCopy M (four r0 r1 r2 r3) (four c0 c1 c2 c3) ↔
      IncreasingFour M.rowBefore r0 r1 r2 r3 ∧
      IncreasingFour M.colBefore c0 c1 c2 c3 ∧
      M.value r0 c0 = false ∧ M.value r0 c1 = true ∧
      M.value r0 c2 = true ∧ M.value r0 c3 = false ∧
      M.value r1 c0 = true ∧ M.value r1 c1 = false ∧
      M.value r1 c2 = false ∧ M.value r1 c3 = true ∧
      M.value r2 c0 = true ∧ M.value r2 c1 = false ∧
      M.value r2 c2 = true ∧ M.value r2 c3 = false ∧
      M.value r3 c0 = false ∧ M.value r3 c1 = true ∧
      M.value r3 c2 = true ∧ M.value r3 c3 = true := by
  simp only [MatrixCopy, four_increasing_iff]
  simp [Fin.forall_fin_succ, four, pattern, and_assoc]

end H4Formal
