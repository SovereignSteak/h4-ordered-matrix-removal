import Lean

namespace H4Formal

theorem bool_guard_or (p q : Prop) : p ∨ (¬ p ∧ q) ↔ p ∨ q := by
  classical
  by_cases hp : p <;> simp [hp]

theorem bool_guard_and (p q : Prop) : p ∧ (¬ p ∨ q) ↔ p ∧ q := by
  classical
  by_cases hp : p <;> simp [hp]

theorem bool_guard_or_flip (p q : Prop) : (p ∧ q) ∨ ¬ p ↔ ¬ p ∨ q := by
  classical
  by_cases hp : p <;> simp [hp]

theorem bool_guard_not_or (p q : Prop) : ¬ p ∨ (p ∧ q) ↔ ¬ p ∨ q := by
  classical
  by_cases hp : p <;> simp [hp]

theorem bool_guard_not_and (p q : Prop) : ¬ p ∧ (p ∨ q) ↔ ¬ p ∧ q := by
  classical
  by_cases hp : p <;> simp [hp]

end H4Formal
