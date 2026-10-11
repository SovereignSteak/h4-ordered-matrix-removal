import Mathlib.Tactic.FinCases

namespace H4Formal

def four {α : Type} (a b c d : α) : Fin 4 → α := fun i =>
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

@[simp] theorem four_zero {α : Type} (a b c d : α) : four a b c d 0 = a := rfl
@[simp] theorem four_one {α : Type} (a b c d : α) : four a b c d 1 = b := rfl
@[simp] theorem four_two {α : Type} (a b c d : α) : four a b c d 2 = c := rfl
@[simp] theorem four_three {α : Type} (a b c d : α) : four a b c d 3 = d := rfl

theorem four_ext {α : Type} (f : Fin 4 → α) (a b c d : α)
    (h0 : f 0 = a) (h1 : f 1 = b) (h2 : f 2 = c) (h3 : f 3 = d) :
    f = four a b c d := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end H4Formal
