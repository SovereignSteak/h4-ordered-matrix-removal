import Lean

namespace H4Formal

theorem square_le_two_pow (t : Nat) (ht : 4 ≤ t) : t * t ≤ 2 ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases he : t < 4
      · have hte : t = 3 := by omega
        subst t; decide
      · have hp := ih (by omega)
        have hl : 3 * t ≤ t * t := Nat.mul_le_mul_right t (by omega)
        have hs : (t + 1) * (t + 1) ≤ 2 * (t * t) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          omega
        exact Nat.le_trans hs (by simpa [Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 hp)

theorem linear_power_exponent_bound (k t : Nat) (ht : 4 * k + 4 ≤ t) :
    t + k * (t + 4) ≤ t * t := by
  have ht4 : t + 4 ≤ 2 * t := by omega
  have hk : 2 * k + 1 ≤ t := by omega
  have hprod := Nat.mul_le_mul_left k ht4
  have hbig := Nat.mul_le_mul_right t hk
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hbig
  have hr : k * (2 * t) = (2 * k) * t := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  rw [hr, Nat.mul_assoc] at hprod
  exact Nat.le_trans (Nat.add_le_add_left hprod t) (by simpa [Nat.add_comm] using hbig)

/-- An explicit arbitrarily deep subsequence beats every integer polynomial. -/
theorem exponential_beats_depth_polynomial (k K H : Nat) :
    ∃ h, 1 ≤ h ∧ H ≤ h ∧ K * (14 * h + 2) ^ k < 4 ^ h := by
  let t := 4 * k + 4 + K + H
  let h := 2 ^ t
  have ht : 4 * k + 4 ≤ t := by omega
  have ht4 : 4 ≤ t := by omega
  have hK : K ≤ 2 ^ t := Nat.le_trans (by omega : K ≤ t) (Nat.le_of_lt Nat.lt_two_pow_self)
  have hH : H ≤ h := Nat.le_trans (by omega : H ≤ t) (Nat.le_of_lt Nat.lt_two_pow_self)
  have hh : 1 ≤ h := Nat.pow_pos (by decide)
  have hs : 14 * h + 2 ≤ 2 ^ (t + 4) := by
    rw [Nat.pow_add]
    change 14 * h + 2 ≤ h * 16
    omega
  have hp := Nat.mul_le_mul hK (Nat.pow_le_pow_left hs k)
  have hp' : K * (14 * h + 2) ^ k ≤ 2 ^ (t + k * (t + 4)) := by
    calc
      K * (14 * h + 2) ^ k ≤ 2 ^ t * (2 ^ (t + 4)) ^ k := hp
      _ = 2 ^ (t + k * (t + 4)) := by rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_comm (t + 4) k]
  have he := linear_power_exponent_bound k t ht
  have hex : t + k * (t + 4) < 2 * h := by
    have hn := square_le_two_pow t ht4
    change t * t ≤ h at hn
    omega
  have hlt : 2 ^ (t + k * (t + 4)) < 4 ^ h := by
    have ho := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hex
    simpa [Nat.pow_mul] using ho
  exact ⟨h, hh, hH, Nat.lt_of_le_of_lt hp' hlt⟩

end H4Formal
