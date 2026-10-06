import CollatzSearch.Runs

/-!
# Rotation invariance and multiplicativity of `oddRuns`

* `oddRuns_add`: cocycle `oddRuns (a+b) n = oddRuns a n + oddRuns b (T^a n)`.
* `oddRuns_rotate`: on a cycle `T^L x = x`, `oddRuns L (T^i x) = oddRuns L x` for all `i`.
* `oddRuns_mul`: on a cycle `T^L x = x`, `oddRuns (t L) x = t · oddRuns L x`.
* `oddSteps_mul`: the same for `oddSteps` (the cocycle `oddSteps_add` and rotation invariance
  `oddSteps_cycle_invariant` are already in `CycleInvariance.lean` and are reused).

Qualifier: `oddRuns L x` equals the number of maximal cyclic odd runs
of the cycle only **when `L` is the minimal period and the cycle contains both parities**.
For a non-minimal period `L = t·p` (`p` minimal), `oddRuns_mul` shows
`oddRuns L x = t · oddRuns p x`, i.e. the count is multiplied by `t`.

Honesty: elementary bookkeeping, not new mathematics; reusable toward the
"exactly `r` runs ⇒ `r`-circuit" bridge.
-/

namespace CollatzSearch
open CollatzProof

/-- Cocycle: `oddRuns (a+b) n = oddRuns a n + oddRuns b (T^a n)`. -/
theorem oddRuns_add (a b n : ℕ) : oddRuns (a + b) n = oddRuns a n + oddRuns b (T^[a] n) := by
  induction a generalizing n with
  | zero => simp [oddRuns]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [oddRuns, ih (T n), Function.iterate_succ_apply]
    omega

/-- `oddRuns 1 n = runStart n`. -/
theorem oddRuns_one (n : ℕ) : oddRuns 1 n = runStart n := by simp [oddRuns]

/-- On a cycle `T^L x = x`: `oddRuns L (T x) = oddRuns L x`. -/
theorem oddRuns_rotate_one {L x : ℕ} (h : T^[L] x = x) : oddRuns L (T x) = oddRuns L x := by
  have e1 : oddRuns (L + 1) x = oddRuns L (T x) + runStart x := rfl
  have e2 := oddRuns_add L 1 x
  rw [h, oddRuns_one] at e2
  omega

/-- **Rotation invariance.** On a cycle `T^L x = x`: `oddRuns L (T^i x) = oddRuns L x`. -/
theorem oddRuns_rotate {L x : ℕ} (h : T^[L] x = x) (i : ℕ) : oddRuns L (T^[i] x) = oddRuns L x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', oddRuns_rotate_one (iterate_cycle h i), ih]

/-- `T^L x = x ⇒ T^{tL} x = x`. -/
theorem iterate_mul_cycle {L x : ℕ} (h : T^[L] x = x) (t : ℕ) : T^[t * L] x = x := by
  rw [mul_comm]; exact Function.IsPeriodicPt.mul_const h t

/-- **Multiplicativity.** On a cycle `T^L x = x`: `oddRuns (t L) x = t · oddRuns L x`. -/
theorem oddRuns_mul {L x : ℕ} (h : T^[L] x = x) (t : ℕ) : oddRuns (t * L) x = t * oddRuns L x := by
  induction t with
  | zero => simp [oddRuns]
  | succ t ih =>
    rw [Nat.succ_mul, oddRuns_add, ih, iterate_mul_cycle h t, Nat.succ_mul]

/-- On a cycle `T^L x = x`: `oddSteps (t L) x = t · oddSteps L x`. -/
theorem oddSteps_mul {L x : ℕ} (h : T^[L] x = x) (t : ℕ) : oddSteps (t * L) x = t * oddSteps L x := by
  induction t with
  | zero => simp [oddSteps]
  | succ t ih =>
    rw [Nat.succ_mul, oddSteps_add, ih, iterate_mul_cycle h t, Nat.succ_mul]

/-- Non-vacuity: rotation on the trivial cycle (`T 1 = 2`). -/
example : oddRuns 2 (T 1) = oddRuns 2 1 := by decide
/-- Non-vacuity: going round the trivial cycle three times counts three runs. -/
example : oddRuns (3 * 2) 1 = 3 := by decide
example : oddRuns (3 * 2) 1 = 3 * oddRuns 2 1 := oddRuns_mul (by decide) 3

end CollatzSearch

#print axioms CollatzSearch.oddRuns_add
#print axioms CollatzSearch.oddRuns_one
#print axioms CollatzSearch.oddRuns_rotate_one
#print axioms CollatzSearch.oddRuns_rotate
#print axioms CollatzSearch.iterate_mul_cycle
#print axioms CollatzSearch.oddRuns_mul
#print axioms CollatzSearch.oddSteps_mul
