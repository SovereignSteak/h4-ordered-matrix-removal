import H4Formal.RealAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed

namespace H4Formal

open Filter Topology

theorem depth_multiplier_tendsto :
    Tendsto (fun h : Nat => 14 * h + 2) atTop atTop :=
  tendsto_atTop_mono (fun h => by omega : ∀ h : Nat, h ≤ 14 * h + 2) tendsto_id

theorem hostSize_tendsto : Tendsto hostSize atTop atTop :=
  tendsto_atTop_mono hostSize_ge_depth tendsto_id

theorem epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) :=
  (tendsto_const_div_pow (1 : ℝ) 2 (by decide)).comp depth_multiplier_tendsto

theorem depth_polynomial_over_exponential_tendsto (k : Nat) :
    Tendsto (fun h : Nat => 3 * ((14 * h + 2 : Nat) : ℝ) ^ k / (4 : ℝ) ^ h)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun h : Nat => (3 * (16 : ℝ) ^ k) * ((h : ℝ) ^ k / (4 : ℝ) ^ h))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : 1 < (4 : ℝ))).const_mul
        (3 * (16 : ℝ) ^ k)
  refine squeeze_zero' (Eventually.of_forall (fun h => by positivity)) ?_ ht
  filter_upwards [eventually_ge_atTop (1 : Nat)] with h hh
  have hd : ((14 * h + 2 : Nat) : ℝ) ≤ (16 : ℝ) * h := by
    exact_mod_cast (by omega : 14 * h + 2 ≤ 16 * h)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ((14 * h + 2 : Nat) : ℝ)) hd k
  calc
    _ ≤ 3 * ((16 : ℝ) * h) ^ k / (4 : ℝ) ^ h :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem copyDensity_nonnegative (h : Nat) : 0 ≤ copyDensity h := by
  unfold copyDensity
  positivity

/-- The counting premise is discharged by the exhaustive classification in GlobalTheorems. -/
theorem copy_ratio_tendsto_of_count
    (hc : ∀ h : Nat, 1 ≤ h →
      hostCopyCount h = 2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5)
    (C : ℝ) : Tendsto (fun h => copyDensity h / (epsilon h) ^ C) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  refine squeeze_zero' (Eventually.of_forall (fun h =>
    div_nonneg (copyDensity_nonnegative h) (Real.rpow_nonneg (epsilon_positive h).le C)))
    ?_ (depth_polynomial_over_exponential_tendsto (2 * k))
  filter_upwards [eventually_ge_atTop (1 : Nat)] with h hh
  have he : epsilon h ^ k = 1 / ((14 * h + 2 : Nat) : ℝ) ^ (2 * k) := by
    simp only [epsilon, div_pow, one_pow, ← pow_mul]
  have hpow : epsilon h ^ k ≤ (epsilon h) ^ C := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (epsilon_positive h) (epsilon_le_one h) hk.le
  calc
    _ ≤ copyDensity h / epsilon h ^ k :=
      div_le_div_of_nonneg_left (copyDensity_nonnegative h)
        (pow_pos (epsilon_positive h) k) hpow
    _ ≤ (3 / (4 : ℝ) ^ h) / epsilon h ^ k :=
      div_le_div_of_nonneg_right (copyDensity_upper_of_count h (hc h hh))
        (pow_pos (epsilon_positive h) k).le
    _ = 3 * ((14 * h + 2 : Nat) : ℝ) ^ (2 * k) / (4 : ℝ) ^ h := by
      rw [he]
      field_simp

end H4Formal
