import H4Formal.TerminalForms
import H4Formal.PhysicalHost

namespace H4Formal

def sameParityPairs (m : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap (fun p =>
    ((List.range p).filter (fun q => decide (q % 2 = p % 2))).map (fun q => (p, q)))

theorem range_parity_count (n b : Nat) (hb : b < 2) :
    (List.range n).countP (fun q => decide (q % 2 = b)) = (n + 1 - b) / 2 := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
      rw [List.range_succ, List.countP_append]
      simp only [List.countP_cons, List.countP_nil]
      rw [ih]
      have hm := Nat.mod_lt n (by decide : 0 < 2)
      by_cases he : n % 2 = b <;> simp [he] <;> omega

theorem sameParity_before_count (p : Nat) :
    ((List.range p).filter (fun q => decide (q % 2 = p % 2))).length = p / 2 := by
  rw [← List.countP_eq_length_filter]
  rw [range_parity_count p (p % 2) (Nat.mod_lt p (by decide))]
  omega

theorem half_sum_even (k : Nat) :
    ((List.range (2 * k)).map (fun p => p / 2)).sum + k = k * k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hr : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [hr, List.range_succ, List.map_append, List.sum_append_nat,
        List.range_succ, List.map_append, List.sum_append_nat]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have hd : (2 * k) / 2 = k := by omega
      have hd' : (2 * k + 1) / 2 = k := by omega
      rw [hd, hd']
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

theorem sameParityPairs_length_even (k : Nat) :
    (sameParityPairs (2 * k)).length = k * (k - 1) := by
  rw [sameParityPairs, List.length_flatMap]
  simp only [List.length_map, sameParity_before_count]
  have hs := half_sum_even k
  by_cases hk : k = 0
  · subst k; simp
  · have he : k * (k - 1) + k = k * k := by
      calc
        k * (k - 1) + k = k * (k - 1) + k * 1 := by simp
        _ = k * (k - 1 + 1) := by rw [Nat.mul_add]
        _ = k * k := by congr 1; omega
    omega

theorem sameParityPairs_length_power (h : Nat) (hh : 1 ≤ h) :
    (sameParityPairs (2 ^ h)).length = 2 ^ (h - 1) * (2 ^ (h - 1) - 1) := by
  have hm : 2 ^ h = 2 * 2 ^ (h - 1) := by
    rw [Nat.mul_comm]
    exact (Nat.two_pow_pred_mul_two hh).symm
  rw [hm, sameParityPairs_length_even]

theorem mem_sameParityPairs (m p q : Nat) :
    (p, q) ∈ sameParityPairs m ↔ p < m ∧ q < p ∧ q % 2 = p % 2 := by
  simp [sameParityPairs]

theorem sameParityPairs_nodup (m : Nat) : (sameParityPairs m).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p _
    apply List.pairwise_map.mpr
    apply (List.nodup_range.filter _).imp
    intro a b hne he
    exact hne (Prod.mk.inj he).2
  · apply List.nodup_range.imp
    intro p q hne a ha b hb he
    rcases List.mem_map.mp ha with ⟨x, _, rfl⟩
    rcases List.mem_map.mp hb with ⟨y, _, rfl⟩
    exact hne (Prod.mk.inj he).1

/-- Multiplicity of each type I tuple: five m-block choices and one two-point parent. -/
theorem terminalI_weight (h p : Nat) (hh : 1 ≤ h) :
    ((blockSize h (terminalRows h p 0) * blockSize h (terminalRows h p 1)) *
      blockSize h (terminalRows h p 2) * blockSize h (terminalRows h p 3)) *
      (blockSize h (terminalIColumns h p 0) * blockSize h (terminalIColumns h p 1) *
      blockSize h (terminalIColumns h p 2) * blockSize h (terminalIColumns h p 3)) =
      2 * (2 ^ h) ^ 5 := by
  have hd : h - (h - 1) = 1 := by omega
  simp [terminalRows, terminalIColumns, four, blockSize, hd, Nat.pow_succ,
    Nat.mul_comm, Nat.mul_left_comm]

/-- Multiplicity of a type II tuple: four m-block choices and one two-point parent. -/
theorem terminalII_weight (h p q : Nat) (hh : 1 ≤ h) :
    (blockSize h (terminalRows h p 0) * blockSize h (terminalRows h p 1) *
      blockSize h (terminalRows h p 2) * blockSize h (terminalRows h p 3)) *
      (blockSize h (terminalIIColumns h p q 0) * blockSize h (terminalIIColumns h p q 1) *
      blockSize h (terminalIIColumns h p q 2) * blockSize h (terminalIIColumns h p q 3)) =
      2 * (2 ^ h) ^ 4 := by
  have hd : h - (h - 1) = 1 := by omega
  simp [terminalRows, terminalIIColumns, four, blockSize, hd, Nat.pow_succ,
    Nat.mul_comm, Nat.mul_left_comm]

def tupleWeight (h : Nat) (r : Fin 4 → Block) : Nat :=
  blockSize h (r 0) * blockSize h (r 1) * blockSize h (r 2) * blockSize h (r 3)

def copyWeight (h : Nat) (r c : Fin 4 → Block) : Nat := tupleWeight h r * tupleWeight h c

def terminalWeightedCount (h : Nat) : Nat :=
  ((List.range (2 ^ h)).map (fun p =>
    copyWeight h (terminalRows h p) (terminalIColumns h p))).sum +
  ((sameParityPairs (2 ^ h)).map (fun pq =>
    copyWeight h (terminalRows h pq.1) (terminalIIColumns h pq.1 pq.2))).sum

theorem terminalWeightedCount_exact (h : Nat) (hh : 1 ≤ h) :
    terminalWeightedCount h = 2 * (2 ^ h) ^ 6 + ((2 ^ h - 2) / 2) * (2 ^ h) ^ 5 := by
  have hI : ((List.range (2 ^ h)).map (fun p =>
      copyWeight h (terminalRows h p) (terminalIColumns h p))) =
      List.replicate (2 ^ h) (2 * (2 ^ h) ^ 5) := by
    have hw : ((List.range (2 ^ h)).map (fun p =>
        copyWeight h (terminalRows h p) (terminalIColumns h p))) =
        List.replicate (List.range (2 ^ h)).length (2 * (2 ^ h) ^ 5) := by
      apply List.map_eq_replicate_iff.mpr
      intro p _
      exact terminalI_weight h p hh
    simpa using hw
  have hII : ((sameParityPairs (2 ^ h)).map (fun pq =>
      copyWeight h (terminalRows h pq.1) (terminalIIColumns h pq.1 pq.2))) =
      List.replicate (sameParityPairs (2 ^ h)).length (2 * (2 ^ h) ^ 4) := by
    apply List.map_eq_replicate_iff.mpr
    intro pq _
    exact terminalII_weight h pq.1 pq.2 hh
  have hm : 2 ^ h = 2 * 2 ^ (h - 1) := by
    rw [Nat.mul_comm]
    exact (Nat.two_pow_pred_mul_two hh).symm
  have hd : (2 ^ h - 2) / 2 = 2 ^ (h - 1) - 1 := by rw [hm]; omega
  unfold terminalWeightedCount
  rw [hI, hII, List.sum_replicate_nat, List.sum_replicate_nat, sameParityPairs_length_power h hh, hd]
  simp [Nat.pow_succ, hm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem terminalRows_parameter_injective (h p q : Nat)
    (he : terminalRows h p = terminalRows h q) : p = q := by
  have hl := congrFun he (2 : Fin 4)
  simpa [terminalRows, four] using (Block.variable.inj hl).2.1

theorem terminalII_parameter_injective (h p q q' : Nat)
    (he : terminalIIColumns h p q = terminalIIColumns h p q') : q = q' := by
  have hl := congrFun he (1 : Fin 4)
  simpa [terminalIIColumns, four] using (Block.variable.inj hl).2.1

theorem terminalForms_disjoint (h p q q' : Nat) :
    terminalIColumns h p ≠ terminalIIColumns h q q' := by
  intro he
  have hl := congrFun he (1 : Fin 4)
  simp [terminalIColumns, terminalIIColumns, four] at hl

end H4Formal
