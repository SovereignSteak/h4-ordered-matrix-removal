import H4Formal.ConcreteWordCompression
import H4Formal.ConcreteCompression

namespace H4Formal

def childWords (bit : Bool) (words : List BinaryWord) : List BinaryWord :=
  words.filterMap (fun u => match u with
    | [] => none
    | b :: tail => if b = bit then some tail else none)

theorem mem_childWords (bit : Bool) (u : BinaryWord) (words : List BinaryWord) :
    u ∈ childWords bit words ↔ bit :: u ∈ words := by
  simp only [childWords, List.mem_filterMap]
  constructor
  · rintro ⟨v, hv, h⟩
    cases v with
    | nil => simp at h
    | cons b tail =>
        by_cases hb : b = bit
        · simp [hb] at h
          subst b
          subst tail
          exact hv
        · simp [hb] at h
  · intro hu
    exact ⟨bit :: u, hu, by simp⟩

theorem childWords_lengths_le (words : List BinaryWord) :
    (childWords false words).length + (childWords true words).length ≤ words.length := by
  induction words with
  | nil => simp [childWords]
  | cons u words ih =>
      cases u with
      | nil => simpa [childWords] using Nat.le_trans ih (Nat.le_succ _)
      | cons b tail =>
          cases b <;> simp [childWords] at * <;> omega

def allBranchLevelsFrom : Nat → Nat → List BinaryWord → List Nat
  | 0, _, _ => []
  | fuel + 1, p, words =>
      let left := childWords false words
      let right := childWords true words
      let sub := allBranchLevelsFrom fuel (p + 1) left ++
        allBranchLevelsFrom fuel (p + 1) right
      if left = [] ∨ right = [] then sub else (p + 1) :: sub

theorem allBranchLevelsFrom_length_bound (fuel p : Nat) (words : List BinaryWord) :
    (allBranchLevelsFrom fuel p words).length ≤ words.length - 1 := by
  induction fuel generalizing p words with
  | zero => simp [allBranchLevelsFrom]
  | succ fuel ih =>
      have hl := ih (p + 1) (childWords false words)
      have hr := ih (p + 1) (childWords true words)
      have hs := childWords_lengths_le words
      by_cases he : childWords false words = [] ∨ childWords true words = []
      · simp only [allBranchLevelsFrom, he, ↓reduceIte, List.length_append]
        rcases he with he | he
        · rw [he] at hl hs ⊢
          simp only [List.length_nil, Nat.zero_add, Nat.zero_sub] at hl hs
          omega
        · rw [he] at hr hs ⊢
          simp only [List.length_nil, Nat.add_zero, Nat.zero_sub] at hr hs
          omega
      · have hleft : 0 < (childWords false words).length := by
          by_cases hz : (childWords false words).length = 0
          · exact False.elim (he (Or.inl (List.length_eq_zero_iff.mp hz)))
          · omega
        have hright : 0 < (childWords true words).length := by
          by_cases hz : (childWords true words).length = 0
          · exact False.elim (he (Or.inr (List.length_eq_zero_iff.mp hz)))
          · omega
        simp only [allBranchLevelsFrom, he, ↓reduceIte,
          List.length_cons, List.length_append]
        omega

theorem allBranchLevelsFrom_covers (fuel p : Nat) (words : List BinaryWord)
    (hlen : ∀ u ∈ words, u.length ≤ fuel)
    {u v : BinaryWord} {d : Nat} (hu : u ∈ words) (hv : v ∈ words)
    (hfd : firstDifference u v = some d) :
    p + d ∈ allBranchLevelsFrom fuel p words := by
  induction fuel generalizing p words u v d with
  | zero =>
      have hu0 : u = [] := List.length_eq_zero_iff.mp (by have := hlen u hu; omega)
      subst u
      cases v <;> simp [firstDifference] at hfd
  | succ fuel ih =>
      cases u with
      | nil => cases v <;> simp [firstDifference] at hfd
      | cons a u =>
          cases v with
          | nil => simp [firstDifference] at hfd
          | cons b v =>
              by_cases hab : a = b
              · subst b
                cases htail : firstDifference u v with
                | none => simp [firstDifference, htail] at hfd
                | some e =>
                    have hde : e + 1 = d := by simpa [firstDifference, htail] using hfd
                    have hchild : ∀ t ∈ childWords a words, t.length ≤ fuel := by
                      intro t ht
                      have ht' := (mem_childWords a t words).mp ht
                      have := hlen (a :: t) ht'
                      simp at this
                      omega
                    have hm := ih (p + 1) (childWords a words) hchild
                      ((mem_childWords a u words).mpr hu)
                      ((mem_childWords a v words).mpr hv) htail
                    have heq : p + d = (p + 1) + e := by omega
                    rw [heq]
                    cases a <;>
                      simp only [allBranchLevelsFrom] <;> split <;>
                      simp_all only [List.mem_cons, List.mem_append, or_true, true_or]
              · have hde : 1 = d := by simpa [firstDifference, hab] using hfd
                have he : ¬ (childWords false words = [] ∨ childWords true words = []) := by
                  have ha := (mem_childWords a u words).mpr hu
                  have hb := (mem_childWords b v words).mpr hv
                  cases a <;> cases b <;> simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true]
                  all_goals intro he; rcases he with he | he <;> simp_all
                simp [allBranchLevelsFrom, he, ← hde]

def actualRetainedLevels (h : Nat) (defining : List Nat)
    (words : List BinaryWord) : List Nat :=
  strictInsertAll [] ([0, h] ++ defining ++ predecessors defining ++
    allBranchLevelsFrom h 0 words)

theorem actualRetainedLevels_sorted (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    List.Pairwise (fun a b => a < b) (actualRetainedLevels h defining words) :=
  strictInsertAll_sorted _

theorem actualRetainedLevels_mem (h : Nat) (defining : List Nat)
    (words : List BinaryWord) {d : Nat}
    (hd : d = 0 ∨ d = h ∨ d ∈ defining ∨ d ∈ predecessors defining ∨
      d ∈ allBranchLevelsFrom h 0 words) :
    d ∈ actualRetainedLevels h defining words := by
  apply strictInsertAll_mem_of_mem
  right
  simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, false_or, or_assoc] using hd

theorem actualRetainedLevels_length_bound (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    (actualRetainedLevels h defining words).length ≤
      2 + 2 * defining.length + (words.length - 1) := by
  have hb := allBranchLevelsFrom_length_bound h 0 words
  have hp := predecessors_length_le defining
  have hs := strictInsertAll_length_le []
    ([0, h] ++ defining ++ predecessors defining ++ allBranchLevelsFrom h 0 words)
  simp only [List.length_append, List.length_cons, List.length_nil] at hs
  change (strictInsertAll [] _).length ≤ _
  omega

def actualProjectedWitness (h : Nat) (defining : List Nat) (words : List BinaryWord)
    (hlen : ∀ u ∈ words, u.length ≤ h)
    (hdef : ∀ u ∈ words, u.length ∈ defining) :
    SelectedWordCompressionWitness words :=
  projectedWordWitness (actualRetainedLevels h defining words) words
    (fun hu => actualRetainedLevels_mem h defining words (Or.inr (Or.inr (Or.inl (hdef _ hu)))))
    (fun hu hv hfd => actualRetainedLevels_mem h defining words
      (Or.inr (Or.inr (Or.inr (Or.inr (by
        simpa using allBranchLevelsFrom_covers h 0 words hlen hu hv hfd))))))

theorem interval_count_split (levels : List Nat) (p n : Nat) :
    levels.countP (fun d => p < d && d ≤ p + (n + 1)) =
      levels.count (p + 1) +
        levels.countP (fun d => p + 1 < d && d ≤ (p + 1) + n) := by
  induction levels with
  | nil => simp
  | cons d levels ih =>
      simp only [List.countP_cons, List.count_cons, ih]
      by_cases hd : d = p + 1
      · subst d
        simp
        omega
      · have he : (p < d ∧ d ≤ p + (n + 1)) ↔
            (p + 1 < d ∧ d ≤ (p + 1) + n) := by omega
        by_cases hi : p < d ∧ d ≤ p + (n + 1)
        · have hj := he.mp hi
          simp [hi.1, hi.2, hj.1, hj.2, hd]
          omega
        · have hj : ¬ (p + 1 < d ∧ d ≤ (p + 1) + n) := by
            exact fun h => hi (he.mpr h)
          have ha : (decide (p < d) && decide (d ≤ p + (n + 1))) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          have hb : (decide (p + 1 < d) && decide (d ≤ (p + 1) + n)) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          simp [ha, hb, hd]

theorem projectCount_eq_interval_count (levels : List Nat)
    (hn : levels.Nodup) (p n : Nat) :
    projectCount levels p n =
      levels.countP (fun d => p < d && d ≤ p + n) := by
  induction n generalizing p with
  | zero =>
      simp only [projectCount]
      symm
      apply List.countP_eq_zero.mpr
      intro d _
      simp
  | succ n ih =>
      rw [projectCount, ih, interval_count_split, hn.count]

theorem retainedDepth_le_card (levels : List Nat) (hn : levels.Nodup)
    (hz : 0 ∈ levels) (h : Nat) :
    retainedDepth levels h ≤ levels.length - 1 := by
  rw [retainedDepth, projectCount_eq_interval_count levels hn,
    List.countP_eq_length_filter]
  have hlt : (levels.filter (fun d => 0 < d && d ≤ 0 + h)).length < levels.length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨0, hz, by simp⟩
  omega

theorem actualRetainedDepth_le_24 (h : Nat) (defining : List Nat)
    (words : List BinaryWord) (hdef : defining.length ≤ 8) (hw : words.length ≤ 8) :
    retainedDepth (actualRetainedLevels h defining words) h ≤ 24 := by
  have hs := actualRetainedLevels_sorted h defining words
  have hn := hs.imp (by intro a b hab; exact Nat.ne_of_lt hab)
  have hz := actualRetainedLevels_mem h defining words (Or.inl rfl)
  have hc := retainedDepth_le_card _ hn hz h
  have hb := actualRetainedLevels_length_bound h defining words
  omega

theorem actualRetainedDepth_pos (h : Nat) (defining : List Nat)
    (words : List BinaryWord) (hh : 0 < h) :
    0 < retainedDepth (actualRetainedLevels h defining words) h := by
  exact projectCount_pos_of_mem _ 0 h hh
    (by simpa using actualRetainedLevels_mem h defining words (Or.inr (Or.inl rfl)))

def parentSupport (words : List BinaryWord) : List BinaryWord :=
  words ++ words.map parentWord

theorem parentSupport_extension (words : List BinaryWord) {u : BinaryWord}
    (hu : u ∈ parentSupport words) :
    ∃ v ∈ words, u <+: v := by
  simp only [parentSupport, List.mem_append, List.mem_map] at hu
  rcases hu with hu | ⟨v, hv, rfl⟩
  · exact ⟨u, hu, List.prefix_rfl⟩
  · exact ⟨v, hv, List.dropLast_prefix v⟩

theorem parentSupport_depth_retained (h : Nat) (defining : List Nat)
    (words : List BinaryWord) (hdef : ∀ u ∈ words, u.length ∈ defining)
    {u : BinaryWord} (hu : u ∈ parentSupport words) :
    u.length ∈ actualRetainedLevels h defining words := by
  simp only [parentSupport, List.mem_append, List.mem_map] at hu
  apply actualRetainedLevels_mem
  rcases hu with hu | ⟨v, hv, rfl⟩
  · exact Or.inr (Or.inr (Or.inl (hdef _ hu)))
  · by_cases hz : v.length = 0
    · exact Or.inl (by simp [parentWord, List.length_dropLast, hz])
    · right; right; right; left
      unfold predecessors
      apply List.mem_filterMap.mpr
      refine ⟨v.length, hdef _ hv, ?_⟩
      simp [hz, parentWord, List.length_dropLast]

def actualParentProjectedWitness (h : Nat) (defining : List Nat)
    (words : List BinaryWord) (hlen : ∀ u ∈ words, u.length ≤ h)
    (hdef : ∀ u ∈ words, u.length ∈ defining) :
    SelectedWordCompressionWitness (parentSupport words) :=
  projectedWordWitness (actualRetainedLevels h defining words) (parentSupport words)
    (parentSupport_depth_retained h defining words hdef)
    (by
      intro u v d hu hv hd
      rcases parentSupport_extension words hu with ⟨u', hu', hp⟩
      rcases parentSupport_extension words hv with ⟨v', hv', hq⟩
      apply actualRetainedLevels_mem
      right; right; right; right
      simpa using allBranchLevelsFrom_covers h 0 words hlen hu' hv'
        (firstDifference_extension hp hq hd))

end H4Formal
