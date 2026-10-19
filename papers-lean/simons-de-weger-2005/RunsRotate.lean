/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Runs

/-!
# Rotation invariance and multiplicativity of `oddRuns`

In this file we prove that the run count `oddRuns` is a cocycle along `T`-orbits. As a
consequence, on a cycle `T^L x = x` the count `oddRuns L x` does not depend on the starting point
of the cycle, and going `t` times round the cycle multiplies it by `t`. The same multiplicativity
holds for the odd-step count `oddSteps`, whose cocycle identity `oddSteps_add` and rotation
invariance `oddSteps_cycle_invariant` are proved in `CycleInvariance`.

Hence `oddRuns L x` is the number of maximal cyclic odd runs of the cycle only when `L` is the
minimal period and the cycle contains both parities; for a period `L = t·p` with `p` minimal,
`oddRuns L x = t · oddRuns p x`.

## Main results

- `oddRuns_add`: `oddRuns (a + b) n = oddRuns a n + oddRuns b (T^a n)`.
- `oddRuns_rotate`: on a cycle `T^L x = x`, `oddRuns L (T^i x) = oddRuns L x` for all `i`.
- `oddRuns_mul`: on a cycle `T^L x = x`, `oddRuns (t L) x = t · oddRuns L x`.
- `oddSteps_mul`: on a cycle `T^L x = x`, `oddSteps (t L) x = t · oddSteps L x`.

## References

- J. L. Simons, B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the
  3n+1-problem*, Acta Arith. 117 (2005), 51–70.
-/

namespace Collatz
open CollatzProof

/-! ### The cocycle identity -/

/-- The run count is a cocycle: `oddRuns (a + b) n = oddRuns a n + oddRuns b (T^a n)`. -/
theorem oddRuns_add (a b n : ℕ) : oddRuns (a + b) n = oddRuns a n + oddRuns b (T^[a] n) := by
  induction a generalizing n with
  | zero => simp [oddRuns]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [oddRuns, ih (T n), Function.iterate_succ_apply]
    omega

theorem oddRuns_one (n : ℕ) : oddRuns 1 n = runStart n := by simp [oddRuns]

/-! ### Rotation invariance -/

/-- On a cycle `T^L x = x`, `oddRuns L (T x) = oddRuns L x`. -/
theorem oddRuns_rotate_one {L x : ℕ} (h : T^[L] x = x) : oddRuns L (T x) = oddRuns L x := by
  have e1 : oddRuns (L + 1) x = oddRuns L (T x) + runStart x := rfl
  have e2 := oddRuns_add L 1 x
  rw [h, oddRuns_one] at e2
  omega

/-- **Rotation invariance.** On a cycle `T^L x = x`, `oddRuns L (T^i x) = oddRuns L x`. -/
theorem oddRuns_rotate {L x : ℕ} (h : T^[L] x = x) (i : ℕ) :
    oddRuns L (T^[i] x) = oddRuns L x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', oddRuns_rotate_one (iterate_cycle h i), ih]

/-! ### Multiplicativity -/

/-- If `T^L x = x`, then `T^{tL} x = x`. -/
theorem iterate_mul_cycle {L x : ℕ} (h : T^[L] x = x) (t : ℕ) : T^[t * L] x = x := by
  rw [mul_comm]; exact Function.IsPeriodicPt.mul_const h t

/-- **Multiplicativity.** On a cycle `T^L x = x`, `oddRuns (t L) x = t · oddRuns L x`. -/
theorem oddRuns_mul {L x : ℕ} (h : T^[L] x = x) (t : ℕ) :
    oddRuns (t * L) x = t * oddRuns L x := by
  induction t with
  | zero => simp [oddRuns]
  | succ t ih =>
    rw [Nat.succ_mul, oddRuns_add, ih, iterate_mul_cycle h t, Nat.succ_mul]

/-- On a cycle `T^L x = x`, `oddSteps (t L) x = t · oddSteps L x`. -/
theorem oddSteps_mul {L x : ℕ} (h : T^[L] x = x) (t : ℕ) :
    oddSteps (t * L) x = t * oddSteps L x := by
  induction t with
  | zero => simp [oddSteps]
  | succ t ih =>
    rw [Nat.succ_mul, oddSteps_add, ih, iterate_mul_cycle h t, Nat.succ_mul]

/-! ### Examples -/

-- Rotation on the trivial cycle (`T 1 = 2`) does not change the run count.
example : oddRuns 2 (T 1) = oddRuns 2 1 := by decide

-- Going round the trivial cycle three times counts three runs.
example : oddRuns (3 * 2) 1 = 3 := by decide

-- The same count obtained from `oddRuns_mul`.
example : oddRuns (3 * 2) 1 = 3 * oddRuns 2 1 := oddRuns_mul (by decide) 3

end Collatz
