import H4Formal.RemovalStatement
import H4Formal.Limits
import H4Formal.Certificates.ClassificationBridge
import H4Formal.Certificates.RepairBridge

namespace H4Formal

theorem classification_exhaustive (h : Nat) (hh : 1 ≤ h) : TerminalExhaustion h := by
  intro r c hc
  have ha := Arithmetic.encode_copy h false r c (by simpa only [quotientHost] using hc)
  have ht := Arithmetic.classification h (by exact_mod_cast hh) _ _ ha
  exact terminal_decodes h hh r c hc ht

theorem classification_iff (h : Nat) (hh : 1 ≤ h) (r c : Fin 4 → Block) :
    ValidCopy h (originalHost h) r c ↔
      ∃ p, p < 2 ^ h ∧ r = terminalRows h p ∧
        (c = terminalIColumns h p ∨
          ∃ q, q < p ∧ q % 2 = p % 2 ∧ c = terminalIIColumns h p q) := by
  constructor
  · exact classification_exhaustive h hh r c
  · rintro ⟨p, hp, rfl, hI | ⟨q, hqp, hpar, hII⟩⟩
    · subst c
      exact terminalI_validCopy h p hh hp
    · subst c
      exact terminalII_validCopy h p q hh hp hqp hpar

theorem canonical_quotient_free (h : Nat) (hh : 1 ≤ h) :
    ∀ r c, ¬ ValidCopy h (canonicalHost h) r c := by
  intro r c hc
  have ha := Arithmetic.encode_copy h true r c (by simpa only [quotientHost] using hc)
  exact Arithmetic.repaired_no_copy h (by exact_mod_cast hh) _ _ ha

theorem canonical_physical_free (h : Nat) (hh : 1 ≤ h) :
    PatternFree (physicalHost h true) := by
  apply (physical_free_iff_quotient_free h true).2
  simpa only [quotientHost] using canonical_quotient_free h hh

theorem canonical_standard_free (h : Nat) (hh : 1 ≤ h) :
    PatternFree (standardHost h true) :=
  (standard_free_iff h true).2 (canonical_physical_free h hh)

theorem exact_copy_count (h : Nat) (hh : 1 ≤ h) :
    hostCopyCount h = 2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 :=
  hostCopyCount_of_exhaustion h hh (classification_exhaustive h hh)

theorem exact_edit_distance (h : Nat) (hh : 1 ≤ h) :
    editDistance (standardHost h) = 2 ^ h * 2 ^ h :=
  standard_distance_of_free_repair h hh (canonical_standard_free h hh)

theorem exact_normalized_distance (h : Nat) (hh : 1 ≤ h) :
    distanceDensity h = epsilon h :=
  distanceDensity_of_free_repair h hh (canonical_standard_free h hh)

theorem normalized_copy_ratio_tendsto (C : ℝ) :
    Filter.Tendsto (fun h => copyDensity h / (epsilon h) ^ C)
      Filter.atTop (nhds 0) :=
  copy_ratio_tendsto_of_count exact_copy_count C

theorem distanceDensity_tendsto_zero :
    Filter.Tendsto distanceDensity Filter.atTop (nhds 0) := by
  apply epsilon_tendsto_zero.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with h hh
  exact (exact_normalized_distance h hh).symm

theorem nonpolynomial_family (c C : ℝ) (hc : 0 < c) (hC : 0 < C) (H : Nat) :
    ∃ h, 1 ≤ h ∧ H ≤ h ∧ H ≤ hostSize h ∧
      distanceDensity h = epsilon h ∧ copyDensity h < c * (epsilon h) ^ C := by
  obtain ⟨h, hh, hH, hsmall⟩ := exponential_density_violation c C hc hC H
  exact ⟨h, hh, hH, hH.trans (hostSize_ge_depth h), exact_normalized_distance h hh,
    (copyDensity_upper_of_count h (exact_copy_count h hh)).trans_lt hsmall⟩

theorem no_polynomial_removal_bound (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ¬ PolynomialRemovalBound c C := by
  intro hb
  obtain ⟨h, hh, _, _, hd, hsmall⟩ := nonpolynomial_family c C hc hC 1
  have hfar : epsilon h ≤ (editDistance (standardHost h) : ℝ) / (hostSize h : ℝ) ^ 2 :=
    hd.symm.le
  have hm := hb (hostSize h) (standardHost h).value (epsilon h)
    (hostSize_positive h) (epsilon_positive h) (epsilon_le_one h)
    (by simpa only [numericMatrix_standardHost] using hfar)
  have hm' : c * (epsilon h) ^ C ≤ copyDensity h := by
    simpa only [numericMatrix_standardHost, matrixCopyCount_standardHost, copyDensity] using hm
  exact (not_lt_of_ge hm') hsmall

/-- Classification, repair, size, count, distance and asymptotics of the host family. -/
theorem end_to_end_main_theorem :
    (∀ h : Nat, 1 ≤ h →
      TerminalExhaustion h ∧ PatternFree (standardHost h true) ∧
      hostSize h = (14 * h + 2) * 2 ^ h ∧
      hostCopyCount h = 2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 ∧
      editDistance (standardHost h) = 2 ^ h * 2 ^ h ∧
      distanceDensity h = epsilon h) ∧
    Filter.Tendsto hostSize Filter.atTop Filter.atTop ∧
    Filter.Tendsto epsilon Filter.atTop (nhds 0) ∧
    (∀ C : ℝ, Filter.Tendsto (fun h => copyDensity h / (epsilon h) ^ C)
      Filter.atTop (nhds 0)) ∧
    (∀ c C : ℝ, 0 < c → 0 < C → ¬ PolynomialRemovalBound c C) := by
  constructor
  · intro h hh
    exact ⟨classification_exhaustive h hh, canonical_standard_free h hh, rfl,
      exact_copy_count h hh, exact_edit_distance h hh, exact_normalized_distance h hh⟩
  · exact ⟨hostSize_tendsto, epsilon_tendsto_zero, normalized_copy_ratio_tendsto,
      no_polynomial_removal_bound⟩

end H4Formal
