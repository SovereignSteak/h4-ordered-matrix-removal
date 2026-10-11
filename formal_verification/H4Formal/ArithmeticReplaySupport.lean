import H4Formal.ReplaySupport

namespace H4Formal

theorem int_eq_bounds (a b : Int) : a = b ↔ a ≤ b ∧ b ≤ a := by omega

theorem int_difference_le_zero (a b : Int) : a + (-1 : Int) * b ≤ 0 ↔ a ≤ b := by omega

theorem int_difference_ge_zero (a b : Int) : 0 ≤ a + (-1 : Int) * b ↔ b ≤ a := by omega

theorem parity_eq_zero (a : Int) : a % 2 = 0 ↔ a % 2 ≤ 0 := by omega

theorem parity_eq_one (a : Int) : a % 2 = 1 ↔ 1 ≤ a % 2 := by omega

end H4Formal
