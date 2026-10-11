import Lean

namespace H4Formal

/-!
# Constructive retained-level bookkeeping

This module isolates the finite combinatorics used by the depth-compression
argument.  A binary word is represented by its bits from the root to the
selected node.  The code constructs adjacent first-divergence labels, removes
duplicate labels, and sorts the resulting retained levels.  The bounds below
are proved in Lean and do not use the SMT corpus.

The semantic host-preservation theorem still consumes the primitive relation
interface in `Transfer.lean`; this file supplies the concrete level budget
which that interface needs.
-/

abbrev BinaryWord := List Bool

def firstDifference : BinaryWord → BinaryWord → Option Nat
  | [], [] => none
  | [], _ :: _ => none
  | _ :: _, [] => none
  | x :: xs, y :: ys =>
      if x = y then
        match firstDifference xs ys with
        | none => none
        | some d => some (d + 1)
      else some 1

def adjacentPairs : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: xs => (a, b) :: adjacentPairs (b :: xs)

def branchLevels (words : List BinaryWord) : List Nat :=
  (adjacentPairs words).filterMap (fun p => firstDifference p.1 p.2)

def predecessors (levels : List Nat) : List Nat :=
  levels.filterMap (fun d => if d = 0 then none else some (d - 1))

def rawRetainedLevels (h : Nat) (defining : List Nat)
    (words : List BinaryWord) : List Nat :=
  [0, h] ++ defining ++ predecessors defining ++ branchLevels words

def natLe (a b : Nat) : Bool := decide (a ≤ b)

def retainedLevels (h : Nat) (defining : List Nat)
    (words : List BinaryWord) : List Nat :=
  List.mergeSort ((rawRetainedLevels h defining words).eraseDups) natLe

theorem adjacentPairs_length (xs : List α) :
    (adjacentPairs xs).length = xs.length - 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          simp [adjacentPairs, ih]

theorem branchLevels_length_le (words : List BinaryWord) :
    (branchLevels words).length ≤ words.length - 1 := by
  change (List.filterMap (fun p => firstDifference p.1 p.2)
      (adjacentPairs words)).length ≤ words.length - 1
  calc
    _ ≤ (adjacentPairs words).length := List.length_filterMap_le _ _
    _ = words.length - 1 := adjacentPairs_length words

theorem predecessors_length_le (levels : List Nat) :
    (predecessors levels).length ≤ levels.length := by
  exact List.length_filterMap_le _ _

theorem eraseDups_length_le_aux {T : Type} [BEq T] (n : Nat)
    (xs : List T) (hx : xs.length ≤ n) :
    xs.eraseDups.length ≤ xs.length := by
  induction n generalizing xs with
  | zero =>
      have hnil : xs = [] := by
        cases xs <;> simp_all
      subst xs
      simp
  | succ n ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
          simp at hx
          rw [List.eraseDups_cons]
          have hf := List.length_filter_le (fun b : T => !b == x) xs
          have hxs : xs.length ≤ n := by omega
          have hfilter : (List.filter (fun b : T => !b == x) xs).length ≤ n :=
            Nat.le_trans hf hxs
          have hd := ih (List.filter (fun b : T => !b == x) xs) hfilter
          change (List.filter (fun b : T => !b == x) xs).eraseDups.length + 1 ≤
            xs.length + 1
          omega

theorem eraseDups_length_le {T : Type} [BEq T] (xs : List T) :
    xs.eraseDups.length ≤ xs.length :=
  eraseDups_length_le_aux xs.length xs (Nat.le_refl _)

theorem rawRetainedLevels_length_le (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    (rawRetainedLevels h defining words).length ≤
      2 + 2 * defining.length + (words.length - 1) := by
  have hp := predecessors_length_le defining
  have hb := branchLevels_length_le words
  simp [rawRetainedLevels, List.length_append] at *
  omega

theorem retainedLevels_length_le_raw (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    (retainedLevels h defining words).length ≤
      (rawRetainedLevels h defining words).length := by
  calc
    (retainedLevels h defining words).length =
        (rawRetainedLevels h defining words).eraseDups.length := by
      simpa [retainedLevels] using
        (List.mergeSort_perm
          (rawRetainedLevels h defining words).eraseDups natLe).length_eq
    _ ≤ (rawRetainedLevels h defining words).length :=
      eraseDups_length_le _

theorem retainedLevels_length_bound (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    (retainedLevels h defining words).length ≤
      2 + 2 * defining.length + (words.length - 1) := by
  exact Nat.le_trans (retainedLevels_length_le_raw h defining words)
    (rawRetainedLevels_length_le h defining words)

theorem retained_depth_le_24_of_eight_records
    (h : Nat) (defining : List Nat) (words : List BinaryWord)
    (hdef : defining.length ≤ 8) (hwords : words.length ≤ 8) :
    (retainedLevels h defining words).length - 1 ≤ 24 := by
  have hb := retainedLevels_length_bound h defining words
  omega

theorem retained_depth_le_six_k_of_records
    (k h : Nat) (defining : List Nat) (words : List BinaryWord)
    (hk : 1 ≤ k)
    (hdef : defining.length ≤ 2 * k) (hwords : words.length ≤ 2 * k) :
    (retainedLevels h defining words).length - 1 ≤ 6 * k := by
  have hb := retainedLevels_length_bound h defining words
  omega

theorem natLe_trans (a b c : Nat) :
    natLe a b = true → natLe b c = true → natLe a c = true := by
  simp [natLe]
  omega

theorem natLe_total (a b : Nat) :
    (natLe a b || natLe b a) = true := by
  simp [natLe]
  omega

theorem retainedLevels_sorted (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    List.Pairwise (fun a b => a ≤ b)
      (retainedLevels h defining words) := by
  have hs := List.sorted_mergeSort natLe_trans natLe_total
    ((rawRetainedLevels h defining words).eraseDups)
  simpa [retainedLevels, natLe] using hs

theorem retainedLevels_perm_dedup (h : Nat) (defining : List Nat)
    (words : List BinaryWord) :
    (retainedLevels h defining words).Perm
      (rawRetainedLevels h defining words).eraseDups := by
  simpa [retainedLevels] using
    (List.mergeSort_perm
      (rawRetainedLevels h defining words).eraseDups natLe)

end H4Formal
