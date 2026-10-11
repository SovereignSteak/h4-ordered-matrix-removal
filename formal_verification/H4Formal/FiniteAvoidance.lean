import H4Formal.Gadgets

namespace H4Formal

theorem countP_le_one_of_unique {α : Type} (xs : List α) (hn : xs.Nodup)
    (p : α → Bool) (hu : ∀ x ∈ xs, ∀ y ∈ xs, p x = true → p y = true → x = y) :
    xs.countP p ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hnodup := List.nodup_cons.mp hn
      have htail := ih hnodup.2 (by
        intro a ha b hb hpa hpb
        exact hu a (by simp [ha]) b (by simp [hb]) hpa hpb)
      cases hp : p x with
      | false => simpa [hp] using htail
      | true =>
          have hzero : xs.countP p = 0 := by
            apply List.countP_eq_zero.mpr
            intro y hy hpy
            have heq := hu x (by simp) y (by simp [hy]) hp hpy
            exact hnodup.1 (heq ▸ hy)
          simp [hp, hzero]

theorem countP_or_le {α : Type} (p q : α → Bool) (xs : List α) :
    xs.countP (fun x => p x || q x) ≤ xs.countP p + xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp [hp, hq] at * <;> omega

/-- Finite counting bound for samples hit by a list of cells. -/
theorem finite_union_bound {Sample Cell : Type} (samples : List Sample)
    (edits : List Cell) (hit : Cell → Sample → Bool) (cap : Nat)
    (hcap : ∀ e ∈ edits, samples.countP (hit e) ≤ cap) :
    samples.countP (fun s => edits.any (fun e => hit e s)) ≤ edits.length * cap := by
  induction edits with
  | nil => simp
  | cons e es ih =>
      have he := hcap e (by simp)
      have hes : ∀ a ∈ es, samples.countP (hit a) ≤ cap := by
        intro a ha
        exact hcap a (by simp [ha])
      have hu := countP_or_le (hit e) (fun s => es.any (fun a => hit a s)) samples
      have hi := ih hes
      simp only [List.any_cons, List.length_cons, Nat.succ_mul]
      omega

theorem exists_unhit_sample {Sample Cell : Type} (samples : List Sample)
    (edits : List Cell) (hit : Cell → Sample → Bool) (cap : Nat)
    (hcap : ∀ e ∈ edits, samples.countP (hit e) ≤ cap)
    (hsmall : edits.length * cap < samples.length) :
    ∃ s ∈ samples, ∀ e ∈ edits, hit e s = false := by
  let bad := fun s => edits.any (fun e => hit e s)
  have bound := finite_union_bound samples edits hit cap hcap
  have partition := List.length_eq_countP_add_countP bad (l := samples)
  have positive : 0 < samples.countP (fun s => ¬ bad s) := by
    change samples.countP bad ≤ edits.length * cap at bound
    omega
  obtain ⟨s, hs, hgood⟩ := List.countP_pos_iff.mp positive
  have hn : bad s = false := by simpa using hgood
  refine ⟨s, hs, ?_⟩
  intro e he
  have hefalse := (List.any_eq_false.mp hn) e he
  simpa using hefalse

theorem exists_unhit_sample_uniform {Sample Cell : Type} (samples : List Sample)
    (edits : List Cell) (hit : Cell → Sample → Bool) (threshold cap : Nat)
    (hcap : ∀ e ∈ edits, samples.countP (hit e) ≤ cap)
    (hsize : samples.length = threshold * cap) (hpositive : 0 < cap)
    (hsmall : edits.length < threshold) :
    ∃ s ∈ samples, ∀ e ∈ edits, hit e s = false := by
  apply exists_unhit_sample samples edits hit cap hcap
  rw [hsize]
  exact Nat.mul_lt_mul_of_pos_right hsmall hpositive

/-- An unhit sample with a protected path yields a forbidden copy. -/
theorem not_free_of_avoiding_paths {R C Sample Cell : Type} (M : OrderedMatrix R C)
    (h : Nat) (samples : List Sample) (edits : List Cell)
    (hit : Cell → Sample → Bool) (threshold cap : Nat)
    (hcap : ∀ e ∈ edits, samples.countP (hit e) ≤ cap)
    (hsize : samples.length = threshold * cap) (hpositive : 0 < cap)
    (hsmall : edits.length < threshold)
    (path : ∀ s ∈ samples, (∀ e ∈ edits, hit e s = false) → ProtectedPath M h) :
    ¬ PatternFree M := by
  obtain ⟨s, hs, hgood⟩ := exists_unhit_sample_uniform samples edits hit threshold cap
    hcap hsize hpositive hsmall
  exact protected_path_not_free M h (path s hs hgood)

end H4Formal
