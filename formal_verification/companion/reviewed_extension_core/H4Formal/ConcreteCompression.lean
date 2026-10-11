import H4Formal.Trie

namespace H4Formal

/-!
# Constructive level sets and rank maps

`Compression.lean` uses `mergeSort` and `eraseDups` to expose the numerical
budget. This file adds a second executable presentation of the same set:
strict insertion into a sorted list. The insertion presentation is useful
for proofs because membership, sortedness, and the length bound are all
structural recursion.
-/

def strictInsert (x : Nat) : List Nat -> List Nat
  | [] => [x]
  | y :: ys =>
      if x = y then y :: ys
      else if x < y then x :: y :: ys
      else y :: strictInsert x ys

theorem strictInsert_mem (x a : Nat) (xs : List Nat) :
    a ∈ strictInsert x xs ↔ a = x ∨ a ∈ xs := by
  induction xs with
  | nil => simp [strictInsert]
  | cons y ys ih =>
    by_cases hxy : x = y
    · simp [strictInsert, hxy]
    · by_cases hlt : x < y
      · simp [strictInsert, hxy, hlt]
      · simp [strictInsert, hxy, hlt, ih, or_left_comm]

theorem strictInsert_length_le (x : Nat) (xs : List Nat) :
    (strictInsert x xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [strictInsert]
  | cons y ys ih =>
    by_cases hxy : x = y
    · simp [strictInsert, hxy]
    · by_cases hlt : x < y
      · simp [strictInsert, hxy, hlt]
      · simp [strictInsert, hxy, hlt]
        omega

theorem strictInsert_sorted
    (x : Nat) (xs : List Nat)
    (hs : List.Pairwise (fun a b => a < b) xs) :
    List.Pairwise (fun a b => a < b) (strictInsert x xs) := by
  induction xs with
  | nil => simp [strictInsert]
  | cons y ys ih =>
    have hsplit := List.pairwise_cons.mp hs
    have hhead : ∀ z, z ∈ ys → y < z := hsplit.1
    have htail : List.Pairwise (fun a b => a < b) ys := hsplit.2
    by_cases hxy : x = y
    · rw [show strictInsert x (y :: ys) = y :: ys by simp [strictInsert, hxy]]
      exact hs
    · by_cases hlt : x < y
      · rw [show strictInsert x (y :: ys) = x :: y :: ys by
          simp [strictInsert, hxy, hlt]]
        apply List.pairwise_cons.mpr
        constructor
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hlt
          · exact Nat.lt_trans hlt (hhead z hz)
        · exact hs
      · have hyx : y < x := by omega
        rw [show strictInsert x (y :: ys) = y :: strictInsert x ys by
          simp [strictInsert, hxy, hlt]]
        apply List.pairwise_cons.mpr
        constructor
        · intro z hz
          have hmem := (strictInsert_mem x z ys).mp hz
          rcases hmem with rfl | hmem
          · exact hyx
          · exact hhead z hmem
        · exact ih htail

theorem strictInsert_nodup
    (x : Nat) (xs : List Nat) (hs : List.Pairwise (fun a b => a < b) xs) :
    (strictInsert x xs).Nodup := by
  have h := strictInsert_sorted x xs hs
  exact h.imp (by intro a b hab; exact Nat.ne_of_lt hab)

def strictInsertAll : List Nat -> List Nat -> List Nat
  | acc, [] => acc
  | acc, x :: xs => strictInsertAll (strictInsert x acc) xs

theorem strictInsertAll_sorted_of_acc
    (acc xs : List Nat)
    (hacc : List.Pairwise (fun a b => a < b) acc) :
    List.Pairwise (fun a b => a < b) (strictInsertAll acc xs) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [strictInsertAll]
    apply ih
    exact strictInsert_sorted x acc hacc

theorem strictInsertAll_sorted (xs : List Nat) :
    List.Pairwise (fun a b => a < b) (strictInsertAll [] xs) := by
  exact strictInsertAll_sorted_of_acc [] xs (by simp)

theorem strictInsertAll_length_le (acc xs : List Nat) :
    (strictInsertAll acc xs).length ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp [strictInsertAll]
  | cons x xs ih =>
    simp only [strictInsertAll]
    calc
      (strictInsertAll (strictInsert x acc) xs).length ≤
          (strictInsert x acc).length + xs.length := ih (strictInsert x acc)
      _ ≤ acc.length + (x :: xs).length := by
        have hi := strictInsert_length_le x acc
        simp only [List.length_cons]
        omega

theorem strictInsertAll_mem_of_mem
    (acc xs : List Nat) (a : Nat) (ha : a ∈ acc ∨ a ∈ xs) :
    a ∈ strictInsertAll acc xs := by
  induction xs generalizing acc with
  | nil => exact ha.elim id (fun h => False.elim (by simp at h))
  | cons x xs ih =>
    simp only [strictInsertAll]
    apply ih
    rcases ha with ha | ha
    · exact Or.inl ((strictInsert_mem x a acc).2 (Or.inr ha))
    · simp only [List.mem_cons] at ha
      rcases ha with hxa | ha
      · exact Or.inl ((strictInsert_mem x a acc).2 (Or.inl hxa))
      · exact Or.inr ha

def constructiveRetainedLevels (h : Nat) (defining : List Nat)
    (words : List BinaryWord) : List Nat :=
  strictInsertAll [] (rawRetainedLevels h defining words)

theorem constructiveRetainedLevels_sorted (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    List.Pairwise (fun a b => a < b)
      (constructiveRetainedLevels h defining words) := by
  exact strictInsertAll_sorted _

theorem constructiveRetainedLevels_mem_raw
    (h : Nat) (defining : List Nat) (words : List BinaryWord)
    {d : Nat} (hd : d ∈ rawRetainedLevels h defining words) :
    d ∈ constructiveRetainedLevels h defining words := by
  exact strictInsertAll_mem_of_mem [] _ d (Or.inr hd)

theorem constructiveRetainedLevels_length_le_raw
    (h : Nat) (defining : List Nat) (words : List BinaryWord) :
    (constructiveRetainedLevels h defining words).length ≤
      (rawRetainedLevels h defining words).length := by
  simpa [constructiveRetainedLevels] using
    (strictInsertAll_length_le [] (rawRetainedLevels h defining words))

theorem constructiveRetainedLevels_length_bound
    (h : Nat) (defining : List Nat) (words : List BinaryWord) :
    (constructiveRetainedLevels h defining words).length ≤
      2 + 2 * defining.length + (words.length - 1) := by
  exact Nat.le_trans
    (constructiveRetainedLevels_length_le_raw h defining words)
    (rawRetainedLevels_length_le h defining words)

def rankBelow (levels : List Nat) (d : Nat) : Nat :=
  (levels.filter (fun x => x < d)).length

theorem rankBelow_cons (a d : Nat) (xs : List Nat) :
    rankBelow (a :: xs) d =
      (if a < d then 1 else 0) + rankBelow xs d := by
  by_cases h : a < d <;> simp [rankBelow, h, Nat.add_comm]

theorem rankBelow_lt_of_strict_sorted
    (levels : List Nat)
    (hs : List.Pairwise (fun a b => a < b) levels)
    (a b : Nat) (ha : a ∈ levels) (hb : b ∈ levels) (hab : a < b) :
    rankBelow levels a < rankBelow levels b := by
  induction levels generalizing a b with
  | nil => simp at ha
  | cons z levels ih =>
    have hsplit := List.pairwise_cons.mp hs
    have hhead : ∀ y, y ∈ levels → z < y := hsplit.1
    have htail : List.Pairwise (fun a b => a < b) levels := hsplit.2
    rw [rankBelow_cons, rankBelow_cons]
    simp only [List.mem_cons] at ha hb
    rcases ha with hza | ha
    · rcases hb with hzb | hb
      · omega
      · subst a
        have hzb' : z < b := by omega
        have hzero : rankBelow levels z = 0 := by
          unfold rankBelow
          rw [List.length_eq_zero_iff]
          rw [List.filter_eq_nil_iff]
          intro y hy
          simp [Nat.not_lt.mpr (Nat.le_of_lt (hhead y hy))]
        rw [hzero]
        simp [hzb']
        omega
    · rcases hb with hzb | hb
      · subst b
        have hle := hhead a ha
        omega
      · have hza' : z < a := hhead a ha
        have hzb' : z < b := by omega
        simp [hza', hzb']
        have h := ih htail a b ha hb hab
        omega

theorem rankBelow_eq_of_mem
    (levels : List Nat)
    (hs : List.Pairwise (fun a b => a < b) levels)
    (a b : Nat) (ha : a ∈ levels) (hb : b ∈ levels)
    (heq : rankBelow levels a = rankBelow levels b) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hab | rfl | hba
  · have hlt := rankBelow_lt_of_strict_sorted levels hs a b ha hb hab
    omega
  · rfl
  · have hlt := rankBelow_lt_of_strict_sorted levels hs b a hb ha hba
    omega

theorem rankBelow_strict_mono_on
    (levels : List Nat)
    (hs : List.Pairwise (fun a b => a < b) levels) :
    ∀ {a b}, a ∈ levels → b ∈ levels → a < b →
      rankBelow levels a < rankBelow levels b := by
  intro a b ha hb hab
  exact rankBelow_lt_of_strict_sorted levels hs a b ha hb hab

theorem constructiveRetainedLevels_rank_injective
    (h : Nat) (defining : List Nat) (words : List BinaryWord)
    {a b : Nat}
    (ha : a ∈ constructiveRetainedLevels h defining words)
    (hb : b ∈ constructiveRetainedLevels h defining words) :
    rankBelow (constructiveRetainedLevels h defining words) a =
      rankBelow (constructiveRetainedLevels h defining words) b → a = b := by
  exact rankBelow_eq_of_mem _
    (constructiveRetainedLevels_sorted h defining words) a b ha hb

theorem constructiveRetainedLevels_rank_order
    (h : Nat) (defining : List Nat) (words : List BinaryWord)
    {a b : Nat}
    (ha : a ∈ constructiveRetainedLevels h defining words)
    (hb : b ∈ constructiveRetainedLevels h defining words)
    (hab : a < b) :
    rankBelow (constructiveRetainedLevels h defining words) a <
      rankBelow (constructiveRetainedLevels h defining words) b := by
  exact rankBelow_lt_of_strict_sorted _
    (constructiveRetainedLevels_sorted h defining words) a b ha hb hab

end H4Formal
