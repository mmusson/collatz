/-
Copyright (c) 2026 Mike Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Musson
-/
import CollatzProof.Basic

/-!
# The classical and accelerated formulations agree

The two maps `C` and `T` reach `1` from exactly the same starting points.  This
is proved here, with no `sorry`: it is bookkeeping about interleaving the forced
halving steps, not progress on the conjecture itself.

The main result `reaches_one_iff` is stated pointwise and with no positivity
hypothesis.  Positivity is not needed: in the odd case `n % 2 = 1` already
forces `n ≥ 1`, and for `n = 0` both sides are false, since `C 0 = T 0 = 0`.

`terras_conjecture` is then a corollary of `collatz_conjecture` rather than an
independent open problem, which is the honest accounting — there is only one
hole in this development.

## Main results

* `reaches_one_iff` — pointwise equivalence.  Proved.
* `collatz_iff_terras` — the quantified form.  Proved.
* `terras_conjecture` — corollary of the (still open) `collatz_conjecture`.
-/

namespace CollatzProof

/-- A single `T`-step is a positive number of `C`-steps: one on evens, two on
odds. -/
theorem exists_iterate_C_eq_T (n : ℕ) : ∃ e, 0 < e ∧ T n = C^[e] n := by
  rcases Nat.eq_zero_or_pos (n % 2) with h | h
  · exact ⟨1, Nat.one_pos, by rw [iterate_C_one, T_eq_C_of_even h]⟩
  · exact ⟨2, Nat.succ_pos 1, by rw [iterate_C_two, T_eq_C_C_of_odd (by omega)]⟩

/-- If the accelerated orbit reaches `1`, so does the classical orbit: simply
expand each `T`-step into the `C`-steps it abbreviates. -/
theorem reaches_C_of_reaches_T {n : ℕ} (h : ∃ k, T^[k] n = 1) : ∃ m, C^[m] n = 1 := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing n with
  | zero => exact ⟨0, hk⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply] at hk
    obtain ⟨m, hm⟩ := ih hk
    obtain ⟨e, -, he⟩ := exists_iterate_C_eq_T n
    exact ⟨m + e, by rw [Function.iterate_add_apply, ← he]; exact hm⟩

/-- If the classical orbit reaches `1`, so does the accelerated orbit.

The induction is on the number of `C`-steps.  The only point requiring an
argument is the odd case: compressing two `C`-steps into one `T`-step is only
safe because the intermediate value `3n + 1` is never `1`, so the classical
orbit cannot terminate at a point the accelerated orbit steps over. -/
theorem reaches_T_of_reaches_C : ∀ m n : ℕ, C^[m] n = 1 → ∃ k, T^[k] n = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hm
    by_cases h1 : n = 1
    · exact ⟨0, by simp [h1]⟩
    rcases Nat.eq_zero_or_pos (n % 2) with he | ho
    · -- `n` is even, so one `T`-step matches one `C`-step.
      have hm0 : m ≠ 0 := by rintro rfl; exact h1 hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Function.iterate_succ_apply] at hm
      obtain ⟨k, hk⟩ := ih m' (by omega) (C n) hm
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, T_eq_C_of_even he]; exact hk⟩
    · -- `n` is odd, so one `T`-step matches two `C`-steps.
      have hodd : n % 2 = 1 := by omega
      have hm0 : m ≠ 0 := by rintro rfl; exact h1 hm
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [Function.iterate_one] at hm
        exact C_ne_one_of_odd hodd hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      rw [Function.iterate_add_apply, iterate_C_two] at hm
      obtain ⟨k, hk⟩ := ih m' (by omega) (C (C n)) hm
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, T_eq_C_C_of_odd hodd]; exact hk⟩

/-- **The classical and accelerated orbits reach `1` from the same points.**

No positivity hypothesis: for `n = 0` both sides are false. -/
theorem reaches_one_iff (n : ℕ) : (∃ m, C^[m] n = 1) ↔ (∃ k, T^[k] n = 1) :=
  ⟨fun ⟨m, hm⟩ => reaches_T_of_reaches_C m n hm, reaches_C_of_reaches_T⟩

/-- The quantified form of the equivalence.  An immediate consequence of
`reaches_one_iff`, which is the stronger statement. -/
theorem collatz_iff_terras :
    (∀ n, 0 < n → ∃ k, C^[k] n = 1) ↔ (∀ n, 0 < n → ∃ k, T^[k] n = 1) := by
  constructor
  · exact fun h n hn => (reaches_one_iff n).mp (h n hn)
  · exact fun h n hn => (reaches_one_iff n).mpr (h n hn)

/-- **The Collatz conjecture, Terras form.**  Every positive integer reaches `1`
under iteration of the accelerated map `T`.

This is *not* an independent open problem: it is a corollary of
`collatz_conjecture` via `reaches_one_iff`.  Its `#print axioms` report inherits
`sorryAx` from that one hole and from nowhere else. -/
theorem terras_conjecture (n : ℕ) (hn : 0 < n) : ∃ k, T^[k] n = 1 :=
  (reaches_one_iff n).mp (collatz_conjecture n hn)

section Transport

/-! The equivalence is only worth anything if it moves real data across.  These
two checks transport the orbit of `27` in both directions: `111` classical steps
one way, `70` accelerated steps the other. -/

set_option maxRecDepth 100000 in
/-- The classical orbit of `27` has length `111`; push it through to the
accelerated side. -/
example : ∃ k, T^[k] 27 = 1 := (reaches_one_iff 27).mp ⟨111, by decide⟩

set_option maxRecDepth 100000 in
/-- The accelerated orbit of `27` has length `70`; push it back. -/
example : ∃ m, C^[m] 27 = 1 := (reaches_one_iff 27).mpr ⟨70, by decide⟩

/-- The edge case the missing positivity hypothesis relies on: `0` never
reaches `1`, so both sides of `reaches_one_iff 0` are false. -/
example : ¬ ∃ m, C^[m] 0 = 1 := by
  rintro ⟨m, hm⟩
  induction m with
  | zero => simp at hm
  | succ k ih =>
    rw [Function.iterate_succ_apply, C_zero] at hm
    exact ih hm

end Transport

end CollatzProof

-- The equivalence is genuinely proved: no `sorryAx` in either report.
#print axioms CollatzProof.reaches_one_iff
#print axioms CollatzProof.collatz_iff_terras

-- The Terras form inherits exactly one hole, from the classical conjecture.
#print axioms CollatzProof.terras_conjecture
