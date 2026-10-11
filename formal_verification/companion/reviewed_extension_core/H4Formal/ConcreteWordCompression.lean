import H4Formal.LocalCompression

namespace H4Formal

def projectFrom (levels : List Nat) : Nat → BinaryWord → BinaryWord
  | _, [] => []
  | p, b :: bs =>
      if p + 1 ∈ levels then
        b :: projectFrom levels (p + 1) bs
      else
        projectFrom levels (p + 1) bs

def projectWord (levels : List Nat) (u : BinaryWord) : BinaryWord :=
  projectFrom levels 0 u

def projectCount (levels : List Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | p, n + 1 =>
      (if p + 1 ∈ levels then 1 else 0) + projectCount levels (p + 1) n

def retainedDepth (levels : List Nat) (d : Nat) : Nat :=
  projectCount levels 0 d

theorem projectCount_pos_of_mem (levels : List Nat) :
    ∀ (p n : Nat), 0 < n → p + n ∈ levels →
      0 < projectCount levels p n := by
  intro p n
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
      intro hn hb
      cases n with
      | zero =>
          simp [projectCount, hb]
      | succ n =>
          have htail : (p + 1) + (n + 1) ∈ levels := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hb
          have hi := ih (p + 1) (by omega) htail
          change 0 < (if p + 1 ∈ levels then 1 else 0) +
            projectCount levels (p + 1) (n + 1)
          exact Nat.lt_of_lt_of_le hi (Nat.le_add_left _ _)

theorem projectCount_strict_of_mem (levels : List Nat) :
    ∀ (p a b : Nat), a < b → p + b ∈ levels →
      projectCount levels p a < projectCount levels p b := by
  intro p a b
  induction b generalizing p a with
  | zero =>
      intro hab
      omega
  | succ b ih =>
      intro hab hb
      cases a with
      | zero =>
          have hi := projectCount_pos_of_mem levels p (b + 1) (by omega) hb
          change 0 < projectCount levels p (b + 1)
          exact hi
      | succ a =>
          have hlt : a < b := by omega
          have htail : (p + 1) + b ∈ levels := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hb
          have hi := ih (p + 1) a hlt htail
          change (if p + 1 ∈ levels then 1 else 0) +
              projectCount levels (p + 1) a <
            (if p + 1 ∈ levels then 1 else 0) +
              projectCount levels (p + 1) b
          exact Nat.add_lt_add_left hi _

theorem projectCount_eq_iff_of_mem (levels : List Nat)
    {a b : Nat} (ha : a ∈ levels) (hb : b ∈ levels) :
    projectCount levels 0 a = projectCount levels 0 b ↔ a = b := by
  constructor
  · intro heq
    rcases Nat.lt_trichotomy a b with hlt | rfl | hgt
    · have hs := projectCount_strict_of_mem levels 0 a b hlt (by simpa using hb)
      omega
    · rfl
    · have hs := projectCount_strict_of_mem levels 0 b a hgt (by simpa using ha)
      omega
  · intro h
    simpa [h]

theorem projectCount_lt_iff_of_mem (levels : List Nat)
    {a b : Nat} (ha : a ∈ levels) (hb : b ∈ levels) :
    projectCount levels 0 a < projectCount levels 0 b ↔ a < b := by
  constructor
  · intro h
    by_cases hab : a < b
    · exact hab
    · have hba : b ≤ a := Nat.le_of_not_gt hab
      rcases Nat.eq_or_lt_of_le hba with hEq | hba
      · subst b
        omega
      · have hs := projectCount_strict_of_mem levels 0 b a hba (by simpa using ha)
        omega
  · intro h
    exact projectCount_strict_of_mem levels 0 a b h (by simpa using hb)

@[simp] theorem projectFrom_nil (levels : List Nat) (p : Nat) :
    projectFrom levels p [] = [] := rfl

theorem projectFrom_append (levels : List Nat) (p : Nat)
    (u v : BinaryWord) :
    projectFrom levels p (u ++ v) =
      projectFrom levels p u ++ projectFrom levels (p + u.length) v := by
  induction u generalizing p with
  | nil => simp
  | cons b bs ih =>
      by_cases hp : p + 1 ∈ levels
      · simp [projectFrom, hp, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [projectFrom, hp, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem projectWord_append (levels : List Nat) (u v : BinaryWord) :
    projectWord levels (u ++ v) =
      projectWord levels u ++ projectFrom levels u.length v := by
  simpa [projectWord] using projectFrom_append levels 0 u v

theorem projectFrom_length (levels : List Nat) (p : Nat) (u : BinaryWord) :
    (projectFrom levels p u).length = projectCount levels p u.length := by
  induction u generalizing p with
  | nil => rfl
  | cons b bs ih =>
      by_cases hp : p + 1 ∈ levels
      · simp [projectFrom, projectCount, hp, ih]
        omega
      · simp [projectFrom, projectCount, hp, ih]

theorem projectWord_length (levels : List Nat) (u : BinaryWord) :
    (projectWord levels u).length = retainedDepth levels u.length := by
  simpa [projectWord, retainedDepth] using projectFrom_length levels 0 u

theorem projectWord_prefix_of_prefix (levels : List Nat)
    {u v : BinaryWord} (h : u <+: v) :
    projectWord levels u <+: projectWord levels v := by
  rcases h with ⟨tail, rfl⟩
  refine ⟨projectFrom levels u.length tail, ?_⟩
  symm
  simpa [projectWord] using projectWord_append levels u tail

theorem firstDifference_exists_decomposition {u v : BinaryWord} {d : Nat}
    (hfd : firstDifference u v = some d) :
    ∃ pre a b su sv,
      pre.length + 1 = d ∧
      u = pre ++ a :: su ∧ v = pre ++ b :: sv ∧ a ≠ b := by
  induction u generalizing v d with
  | nil =>
      cases v <;> simp [firstDifference] at hfd
  | cons a u ih =>
      cases v with
      | nil => simp [firstDifference] at hfd
      | cons b v =>
          by_cases hab : a = b
          · subst b
            cases htail : firstDifference u v with
            | none => simp [firstDifference, htail] at hfd
            | some e =>
                have hde : e + 1 = d := by
                  simpa [firstDifference, htail] using hfd
                rcases ih (v := v) (d := e) htail with
                  ⟨pre, x, y, su, sv, hlen, hu, hv, hxy⟩
                refine ⟨a :: pre, x, y, su, sv, ?_, ?_, ?_, hxy⟩
                · simp [hlen, hde, Nat.add_assoc]
                · simp [hu, Nat.add_assoc]
                · simp [hv, Nat.add_assoc]
          · have hd : 1 = d := by
              simpa [firstDifference, hab] using hfd
            refine ⟨[], a, b, u, v, ?_, ?_, ?_, hab⟩
            · simpa using hd
            · simp
            · simp

theorem firstDifference_none_of_prefix {u v : BinaryWord} (h : u <+: v) :
    firstDifference u v = none := by
  rcases h with ⟨tail, rfl⟩
  induction u with
  | nil => cases tail <;> rfl
  | cons a u ih =>
      simp only [List.cons_append, firstDifference]
      simp [ih]

theorem firstDifference_comm (u v : BinaryWord) :
    firstDifference u v = firstDifference v u := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons a u ih =>
      cases v with
      | nil => rfl
      | cons b v =>
          by_cases hab : a = b
          · simp [firstDifference, hab, ih]
          · simp [firstDifference, hab, Ne.symm hab]

theorem firstDifference_none_of_prefix_right {u v : BinaryWord}
    (h : v <+: u) : firstDifference u v = none := by
  rw [firstDifference_comm]
  exact firstDifference_none_of_prefix h

theorem firstDifference_some_of_not_prefix
    {u v : BinaryWord} (huv : ¬ u <+: v) (hvu : ¬ v <+: u) :
    ∃ d, firstDifference u v = some d := by
  induction u generalizing v with
  | nil => simp at huv
  | cons a u ih =>
      cases v with
      | nil => simp at hvu
      | cons b v =>
          by_cases hab : a = b
          · subst b
            have htailu : ¬ u <+: v := by
              intro h
              apply huv
              exact List.cons_prefix_iff.mpr ⟨v, rfl, h⟩
            have htailv : ¬ v <+: u := by
              intro h
              apply hvu
              exact List.cons_prefix_iff.mpr ⟨u, rfl, h⟩
            rcases ih htailu htailv with ⟨d, hd⟩
            exact ⟨d + 1, by simp [firstDifference, hd]⟩
          · exact ⟨1, by simp [firstDifference, hab]⟩

theorem firstDifference_some_iff_not_prefix_not_prefix {u v : BinaryWord} :
    (∃ d, firstDifference u v = some d) ↔
      ¬ u <+: v ∧ ¬ v <+: u := by
  constructor
  · rintro ⟨d, hd⟩
    constructor
    · intro h
      rw [firstDifference_none_of_prefix h] at hd
      cases hd
    · intro h
      rw [firstDifference_none_of_prefix_right h] at hd
      cases hd
  · intro h
    exact firstDifference_some_of_not_prefix h.1 h.2

theorem projectWord_split_at (levels : List Nat)
    (pre : BinaryWord) (a : Bool) (tail : BinaryWord)
    (hlevel : pre.length + 1 ∈ levels) :
    projectWord levels (pre ++ a :: tail) =
      projectFrom levels 0 pre ++
        a :: projectFrom levels (pre.length + 1) tail := by
  change projectFrom levels 0 (pre ++ a :: tail) = _
  rw [projectFrom_append]
  simp [projectFrom, hlevel]

theorem projectWord_not_prefix_of_firstDifference
    (levels : List Nat) {u v : BinaryWord} {d : Nat}
    (hfd : firstDifference u v = some d) (hd : d ∈ levels) :
    ¬ projectWord levels u <+: projectWord levels v := by
  rcases firstDifference_exists_decomposition hfd with
    ⟨pre, a, b, su, sv, hlen, rfl, rfl, hab⟩
  have hlevel : pre.length + 1 ∈ levels := by simpa [hlen] using hd
  rw [projectWord_split_at levels pre a su hlevel]
  rw [projectWord_split_at levels pre b sv hlevel]
  intro hp
  rw [List.prefix_append_right_inj] at hp
  have hab' : a = b := (List.cons_prefix_cons.mp hp).1
  exact hab hab'

@[simp] theorem bitLT_irrefl (b : Bool) : ¬ bitLT b b := by
  cases b <;> simp [bitLT]

theorem binaryLexLess_irrefl (u : BinaryWord) : ¬ binaryLexLess u u := by
  induction u with
  | nil => simp [binaryLexLess]
  | cons b u ih => simpa [binaryLexLess, List.cons_lex_cons_iff] using ih

theorem lex_of_properPrefix {u v : BinaryWord}
    (h : properPrefix u v) : List.Lex bitLT u v := by
  rcases h.1 with ⟨tail, rfl⟩
  have htail : tail ≠ [] := by
    intro hnil
    subst tail
    simp [properPrefix] at h
  induction u generalizing tail with
  | nil =>
      cases tail with
      | nil => contradiction
      | cons b tail => exact List.Lex.nil
  | cons a u ih =>
      cases tail with
      | nil => contradiction
      | cons b tail =>
          apply List.Lex.cons
          apply ih
          simp [properPrefix] at h ⊢
          omega

theorem not_lex_of_properPrefix_reverse {u v : BinaryWord}
    (h : properPrefix v u) : ¬ List.Lex bitLT u v := by
  rcases h.1 with ⟨tail, rfl⟩
  clear h
  induction v with
  | nil => simp
  | cons a v ih =>
      simpa [List.cons_lex_cons_iff] using ih

theorem lex_at_firstDifference
    (pre : BinaryWord) (a b : Bool) (su sv : BinaryWord) (hab : a ≠ b) :
    List.Lex bitLT (pre ++ a :: su) (pre ++ b :: sv) ↔ bitLT a b := by
  induction pre with
  | nil =>
      simp [bitLT, List.cons_lex_cons_iff, hab]
  | cons p pre ih =>
      simpa [List.cons_lex_cons_iff] using ih

theorem projectWord_properPrefix_of_properPrefix
    (levels : List Nat) {u v : BinaryWord}
    (hu : u.length ∈ levels) (hv : v.length ∈ levels)
    (h : properPrefix u v) :
    properPrefix (projectWord levels u) (projectWord levels v) := by
  constructor
  · exact projectWord_prefix_of_prefix levels h.1
  · rw [projectWord_length, projectWord_length]
    exact (projectCount_lt_iff_of_mem levels hu hv).2 h.2

theorem projectWord_prefix_iff_of_support
    (levels : List Nat) (support : List BinaryWord)
    (hdepth : ∀ {u}, u ∈ support → u.length ∈ levels)
    (hdiv : ∀ {u v d}, u ∈ support → v ∈ support →
      firstDifference u v = some d → d ∈ levels)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support) :
    projectWord levels u <+: projectWord levels v ↔ u <+: v := by
  constructor
  · intro hproj
    by_cases huv : u <+: v
    · exact huv
    · by_cases hvu : v <+: u
      · by_cases heq : u = v
        · exact heq ▸ List.prefix_rfl
        · have hproper : properPrefix v u := by
            constructor
            · exact hvu
            · have hle := hvu.length_le
              have hne : v.length ≠ u.length := by
                intro hlen
                apply heq
                exact (hvu.eq_of_length hlen).symm
              omega
          have hprojProper := projectWord_properPrefix_of_properPrefix levels
            (hdepth hv) (hdepth hu) hproper
          have hcontra := hproj.length_le
          have hsmall := hprojProper.2
          omega
      · rcases (firstDifference_some_iff_not_prefix_not_prefix).2
          ⟨huv, hvu⟩ with ⟨d, hfd⟩
        have hd := hdiv hu hv hfd
        exact False.elim (projectWord_not_prefix_of_firstDifference
          levels hfd hd hproj)
  · exact projectWord_prefix_of_prefix levels

theorem projectWord_lex_iff_of_support
    (levels : List Nat) (support : List BinaryWord)
    (hdepth : ∀ {u}, u ∈ support → u.length ∈ levels)
    (hdiv : ∀ {u v d}, u ∈ support → v ∈ support →
      firstDifference u v = some d → d ∈ levels)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support) :
    binaryLexLess (projectWord levels u) (projectWord levels v) ↔
      binaryLexLess u v := by
  change List.Lex bitLT (projectWord levels u) (projectWord levels v) ↔
    List.Lex bitLT u v
  by_cases huv : u <+: v
  · by_cases heq : u = v
    · subst v
      exact iff_of_false (binaryLexLess_irrefl _) (binaryLexLess_irrefl _)
    · have hproper : properPrefix u v := by
        constructor
        · exact huv
        · have hle := huv.length_le
          have hne : u.length ≠ v.length := by
            intro hlen
            apply heq
            exact huv.eq_of_length hlen
          omega
      have hp := projectWord_properPrefix_of_properPrefix levels
        (hdepth hu) (hdepth hv) hproper
      exact iff_of_true (lex_of_properPrefix hp) (lex_of_properPrefix hproper)
  · by_cases hvu : v <+: u
    · have heq : u ≠ v := by
        intro h
        apply huv
        exact h ▸ List.prefix_rfl
      have hproper : properPrefix v u := by
        constructor
        · exact hvu
        · have hle := hvu.length_le
          have hne : v.length ≠ u.length := by
            intro hlen
            exact heq (hvu.eq_of_length hlen).symm
          omega
      have hp := projectWord_properPrefix_of_properPrefix levels
        (hdepth hv) (hdepth hu) hproper
      exact iff_of_false (not_lex_of_properPrefix_reverse hp)
        (not_lex_of_properPrefix_reverse hproper)
    · rcases (firstDifference_some_iff_not_prefix_not_prefix).2
          ⟨huv, hvu⟩ with ⟨d, hfd⟩
      have hd := hdiv hu hv hfd
      rcases firstDifference_exists_decomposition hfd with
        ⟨pre, a, b, su, sv, hlen, huword, vword, hab⟩
      have hlevel : pre.length + 1 ∈ levels := by simpa [hlen] using hd
      have hlex := lex_at_firstDifference pre a b su sv hab
      have hlexProj :
          List.Lex bitLT (projectWord levels u) (projectWord levels v) ↔
            bitLT a b := by
        rw [huword, vword]
        rw [projectWord_split_at levels pre a su hlevel]
        rw [projectWord_split_at levels pre b sv hlevel]
        exact lex_at_firstDifference _ _ _ _ _ hab
      simpa [huword, vword] using hlexProj.trans hlex.symm

theorem projectWord_concat (levels : List Nat) (pre : BinaryWord) (a : Bool)
    (hd : pre.length + 1 ∈ levels) :
    projectWord levels (pre ++ [a]) = projectWord levels pre ++ [a] := by
  simpa [projectWord] using projectWord_split_at levels pre a [] hd

theorem projectWord_endpoint (levels : List Nat) (u : BinaryWord)
    (hd : u.length ∈ levels) :
    endpointBit (projectWord levels u) = endpointBit u := by
  rcases List.eq_nil_or_concat u with rfl | ⟨pre, a, rfl⟩
  · rfl
  · have hlevel : pre.length + 1 ∈ levels := by simpa using hd
    simp only [List.concat_eq_append] at *
    rw [projectWord_concat levels pre a hlevel]
    simp [endpointBit]

theorem projectWord_parent (levels : List Nat) (u : BinaryWord)
    (hd : u.length ∈ levels) :
    parentWord (projectWord levels u) = projectWord levels (parentWord u) := by
  rcases List.eq_nil_or_concat u with rfl | ⟨pre, a, rfl⟩
  · rfl
  · have hlevel : pre.length + 1 ∈ levels := by simpa using hd
    simp only [List.concat_eq_append] at *
    rw [projectWord_concat levels pre a hlevel]
    simp [parentWord]

def projectedWordWitness (levels : List Nat) (support : List BinaryWord)
    (hdepth : ∀ {u}, u ∈ support → u.length ∈ levels)
    (hdiv : ∀ {u v d}, u ∈ support → v ∈ support →
      firstDifference u v = some d → d ∈ levels) :
    SelectedWordCompressionWitness support where
  map := projectWord levels
  depthMap := retainedDepth levels
  length_map := fun u _ => projectWord_length levels u
  depth_order := fun hu hv =>
    projectCount_eq_iff_of_mem levels (hdepth hu) (hdepth hv)
  prefix_iff := projectWord_prefix_iff_of_support levels support hdepth hdiv
  length_lt_iff := by
    intro u v hu hv
    rw [projectWord_length, projectWord_length]
    exact projectCount_lt_iff_of_mem levels (hdepth hu) (hdepth hv)
  lex_iff := projectWord_lex_iff_of_support levels support hdepth hdiv
  first_divergence_defined_iff := by
    intro u v hu hv
    change (∃ d, firstDifference _ _ = some d) ↔
      (∃ d, firstDifference u v = some d)
    rw [firstDifference_some_iff_not_prefix_not_prefix,
      firstDifference_some_iff_not_prefix_not_prefix,
      projectWord_prefix_iff_of_support levels support hdepth hdiv hu hv,
      projectWord_prefix_iff_of_support levels support hdepth hdiv hv hu]
  endpoint_iff := fun hu => projectWord_endpoint levels _ (hdepth hu)
  parent_iff := fun hu => projectWord_parent levels _ (hdepth hu)

theorem firstDifference_append_of_some {u v : BinaryWord} {d : Nat}
    (hfd : firstDifference u v = some d) (su sv : BinaryWord) :
    firstDifference (u ++ su) (v ++ sv) = some d := by
  induction u generalizing v d with
  | nil => cases v <;> simp [firstDifference] at hfd
  | cons a u ih =>
      cases v with
      | nil => simp [firstDifference] at hfd
      | cons b v =>
          by_cases he : a = b
          · subst b
            cases ht : firstDifference u v with
            | none => simp [firstDifference, ht] at hfd
            | some e =>
                have hd : e + 1 = d := by simpa [firstDifference, ht] using hfd
                simp [firstDifference, ih ht, ← hd]
          · simpa [firstDifference, he] using hfd

theorem firstDifference_extension {u v u' v' : BinaryWord} {d : Nat}
    (hu : u <+: u') (hv : v <+: v') (hd : firstDifference u v = some d) :
    firstDifference u' v' = some d := by
  rcases hu with ⟨su, rfl⟩
  rcases hv with ⟨sv, rfl⟩
  exact firstDifference_append_of_some hd su sv

theorem SelectedWordCompressionWitness.map_eq_iff
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support) :
    w.map u = w.map v ↔ u = v := by
  constructor
  · intro he
    have hp : u <+: v := (w.prefix_iff hu hv).mp (by rw [he]; exact List.prefix_rfl)
    have hq : v <+: u := (w.prefix_iff hv hu).mp (by rw [he]; exact List.prefix_rfl)
    exact hp.eq_of_length (Nat.le_antisymm hp.length_le hq.length_le)
  · rintro rfl
    rfl

theorem projectCount_end (levels : List Nat) (p n : Nat) :
    projectCount levels p (n + 1) = projectCount levels p n +
      if p + n + 1 ∈ levels then 1 else 0 := by
  induction n generalizing p with
  | zero => simp [projectCount]
  | succ n ih =>
      change (if p + 1 ∈ levels then 1 else 0) +
          projectCount levels (p + 1) (n + 1) =
        ((if p + 1 ∈ levels then 1 else 0) + projectCount levels (p + 1) n) +
          if p + (n + 1) + 1 ∈ levels then 1 else 0
      rw [ih]
      have he : p + 1 + n + 1 = p + (n + 1) + 1 := by omega
      rw [he]
      omega

theorem retainedDepth_end (levels : List Nat) (n : Nat) :
    retainedDepth levels (n + 1) = retainedDepth levels n +
      if n + 1 ∈ levels then 1 else 0 := by
  simpa [retainedDepth] using projectCount_end levels 0 n

theorem retainedDepth_mono (levels : List Nat) {a b : Nat} (h : a ≤ b) :
    retainedDepth levels a ≤ retainedDepth levels b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst a
            exact Nat.le_refl _
  | succ b ih =>
      by_cases he : a = b + 1
      · rw [he]
        exact Nat.le_refl _
      · have hi := ih (by omega)
        rw [retainedDepth_end]
        omega

theorem retainedDepth_pred (levels : List Nat) (d : Nat) (hd : d ∈ levels) :
    retainedDepth levels (d - 1) = retainedDepth levels d - 1 := by
  cases d with
  | zero => rfl
  | succ d => simp [retainedDepth_end, hd]

theorem retainedDepth_adjacent_iff (levels : List Nat) {a b : Nat}
    (ha : a ∈ levels) (hb : b ∈ levels)
    (hpre : a ≠ 0 → a - 1 ∈ levels) :
    retainedDepth levels a = retainedDepth levels b + 1 ↔ a = b + 1 := by
  constructor
  · intro he
    have hba : b < a := by
      by_cases h : a ≤ b
      · have hi := retainedDepth_mono levels h
        omega
      · omega
    have hp := hpre (by omega)
    by_cases hab : a = b + 1
    · exact hab
    · have hsmall : b < a - 1 := by omega
      have hi := (projectCount_lt_iff_of_mem levels hb hp).mpr hsmall
      change retainedDepth levels b < retainedDepth levels (a - 1) at hi
      rw [retainedDepth_pred levels a ha] at hi
      omega
  · rintro rfl
    simp [retainedDepth_end, ha]

end H4Formal
