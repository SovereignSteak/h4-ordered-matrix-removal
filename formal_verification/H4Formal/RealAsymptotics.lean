import H4Formal.EditDistance
import H4Formal.NumericAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace H4Formal

noncomputable def epsilon (h : Nat) : ℝ := 1 / ((14 * h + 2 : Nat) : ℝ) ^ 2

noncomputable def copyDensity (h : Nat) : ℝ :=
  (hostCopyCount h : ℝ) / (hostSize h : ℝ) ^ 8

noncomputable def distanceDensity (h : Nat) : ℝ :=
  (editDistance (standardHost h) : ℝ) / (hostSize h : ℝ) ^ 2

theorem hostSize_positive (h : Nat) : 0 < hostSize h :=
  Nat.mul_pos (by omega) (Nat.pow_pos (by decide))

theorem hostSize_ge_depth (h : Nat) : h ≤ hostSize h := by
  have hm : 1 ≤ 2 ^ h := Nat.pow_pos (by decide)
  have hd : h ≤ 14 * h + 2 := by omega
  exact hd.trans (by simpa only [Nat.mul_one, hostSize] using Nat.mul_le_mul_left (14 * h + 2) hm)

theorem epsilon_positive (h : Nat) : 0 < epsilon h := by
  unfold epsilon
  positivity

theorem epsilon_le_one (h : Nat) : epsilon h ≤ 1 := by
  have hd : (1 : ℝ) ≤ ((14 * h + 2 : Nat) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 14 * h + 2)
  unfold epsilon
  apply (div_le_one (by positivity)).2
  nlinarith

theorem terminal_count_bound (h : Nat) :
    2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 ≤ 3 * (2 ^ h) ^ 6 := by
  have hq : (2 ^ h - 2) / 2 ≤ 2 ^ h := (Nat.div_le_self ..).trans (Nat.sub_le ..)
  calc
    _ ≤ 2 * (2 ^ h) ^ 6 + (2 ^ h) * (2 ^ h) ^ 5 :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hq) _
    _ = _ := by ring

theorem cast_two_power_square (h : Nat) : ((2 ^ h : Nat) : ℝ) ^ 2 = (4 : ℝ) ^ h := by
  push_cast
  rw [← pow_mul, Nat.mul_comm h 2, pow_mul]
  norm_num

theorem copyDensity_upper_of_count (h : Nat)
    (hc : hostCopyCount h = 2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5) :
    copyDensity h ≤ 3 / (4 : ℝ) ^ h := by
  have hcn : hostCopyCount h ≤ 3 * (2 ^ h) ^ 6 := by rw [hc]; exact terminal_count_bound h
  have hcr : (hostCopyCount h : ℝ) ≤ 3 * ((2 ^ h : Nat) : ℝ) ^ 6 := by exact_mod_cast hcn
  have hm : (0 : ℝ) < ((2 ^ h : Nat) : ℝ) := by exact_mod_cast (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ h)
  have hn : (0 : ℝ) < (hostSize h : ℝ) := by exact_mod_cast hostSize_positive h
  have hmn : (2 ^ h : Nat) ≤ hostSize h := by
    have hd : 1 ≤ 14 * h + 2 := by omega
    simpa only [Nat.one_mul, hostSize] using Nat.mul_le_mul_right (2 ^ h) hd
  have hmnR : ((2 ^ h : Nat) : ℝ) ≤ (hostSize h : ℝ) := by exact_mod_cast hmn
  have hpow : ((2 ^ h : Nat) : ℝ) ^ 8 ≤ (hostSize h : ℝ) ^ 8 :=
    pow_le_pow_left₀ hm.le hmnR 8
  calc
    copyDensity h ≤ 3 * ((2 ^ h : Nat) : ℝ) ^ 6 / (hostSize h : ℝ) ^ 8 :=
      div_le_div_of_nonneg_right hcr (by positivity)
    _ ≤ 3 * ((2 ^ h : Nat) : ℝ) ^ 6 / ((2 ^ h : Nat) : ℝ) ^ 8 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = 3 / (4 : ℝ) ^ h := by
      rw [← cast_two_power_square h]
      field_simp

theorem distanceDensity_of_free_repair (h : Nat) (hh : 1 ≤ h)
    (hf : PatternFree (standardHost h true)) : distanceDensity h = epsilon h := by
  unfold distanceDensity epsilon
  rw [standard_distance_of_free_repair h hh hf]
  simp only [hostSize, Nat.cast_mul]
  have hm : (((2 ^ h : Nat) : ℝ)) ≠ 0 := by positivity
  have hd : (((14 * h + 2 : Nat) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- Real exponents and real constants, with arbitrarily large depth. -/
theorem exponential_density_violation (c C : ℝ) (hc : 0 < c) (_hC : 0 < C) (H : Nat) :
    ∃ h, 1 ≤ h ∧ H ≤ h ∧ 3 / (4 : ℝ) ^ h < c * (epsilon h) ^ C := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  obtain ⟨K, hK⟩ := exists_nat_gt (3 / c)
  obtain ⟨h, hh, hH, hg⟩ := exponential_beats_depth_polynomial (2 * k) K H
  have hgr : (K : ℝ) * ((14 * h + 2 : Nat) : ℝ) ^ (2 * k) < (4 : ℝ) ^ h := by
    exact_mod_cast hg
  have h3 : (3 : ℝ) < c * K := by
    have he := (div_lt_iff₀ hc).1 hK
    simpa only [mul_comm] using he
  have hd : (0 : ℝ) < ((14 * h + 2 : Nat) : ℝ) := by positivity
  have hcross : 3 * ((14 * h + 2 : Nat) : ℝ) ^ (2 * k) < c * (4 : ℝ) ^ h := by
    calc
      _ < (c * K) * ((14 * h + 2 : Nat) : ℝ) ^ (2 * k) :=
        mul_lt_mul_of_pos_right h3 (by positivity)
      _ = c * ((K : ℝ) * ((14 * h + 2 : Nat) : ℝ) ^ (2 * k)) := by ring
      _ < _ := mul_lt_mul_of_pos_left hgr hc
  have hdiv : 3 / (4 : ℝ) ^ h < c / ((14 * h + 2 : Nat) : ℝ) ^ (2 * k) :=
    (div_lt_div_iff₀ (by positivity) (by positivity)).2 hcross
  have hepower : epsilon h ^ k = 1 / ((14 * h + 2 : Nat) : ℝ) ^ (2 * k) := by
    simp only [epsilon, div_pow, one_pow, ← pow_mul]
  have hexponent : epsilon h ^ k ≤ (epsilon h) ^ C := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (epsilon_positive h) (epsilon_le_one h) hk.le
  refine ⟨h, hh, hH, ?_⟩
  calc
    _ < c * epsilon h ^ k := by simpa only [hepower, mul_one_div] using hdiv
    _ ≤ _ := mul_le_mul_of_nonneg_left hexponent hc.le

end H4Formal
