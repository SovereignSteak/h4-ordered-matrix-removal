import Lean

/-!
# Retained-level arithmetic bounds

From the hypotheses `s ≤ 2 + 2*u + b`, `b ≤ v - 1`, and `v ≤ u`, derive
the bounds `s - 1 ≤ 24` for `u ≤ 8` and `s - 1 ≤ 6*k` for `u ≤ 2*k`.
The case `v = 0` gives `s ≤ 18`.
-/

namespace H4Formal

/-- The numeric 24-level conclusion from the specified combinatorial bounds. -/
theorem depth_le_24_of_retained_budget
    (u v b s : Nat)
    (hu : u ≤ 8)
    (hv : v ≤ u)
    (hb : b ≤ v - 1)
    (hs : s ≤ 2 + 2 * u + b)
    (hpositive : 1 ≤ s) :
    s - 1 ≤ 24 := by
  omega

/-- Uniform `6k` specialization for at most k row and k column types. -/
theorem depth_le_six_k_of_retained_budget
    (k u v b s : Nat)
    (hk : 1 ≤ k)
    (hu : u ≤ 2 * k)
    (hv : v ≤ u)
    (hb : b ≤ v - 1)
    (hs : s ≤ 2 + 2 * u + b)
    (hpositive : 1 ≤ s) :
    s - 1 ≤ 6 * k := by
  omega

/-- Retained-level bound when the branching count is zero. -/
theorem no_variable_levels_budget
    (u b s : Nat) (hu : u ≤ 8)
    (hb : b ≤ 0) (hs : s ≤ 2 + 2 * u + b) :
    s ≤ 18 := by
  omega

/-- The h4=4 case agrees algebraically with the 6k statement. -/
theorem depth_le_24_via_general
    (u v b s : Nat)
    (hu : u ≤ 2 * 4)
    (hv : v ≤ u)
    (hb : b ≤ v - 1)
    (hs : s ≤ 2 + 2 * u + b)
    (hpositive : 1 ≤ s) :
    s - 1 ≤ 24 := by
  have h := depth_le_six_k_of_retained_budget 4 u v b s (by omega) hu hv hb hs hpositive
  omega

end H4Formal
