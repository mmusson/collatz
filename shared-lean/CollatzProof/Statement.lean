/-
Copyright (c) 2026 Mike Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Musson
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate

/-!
# The Collatz conjecture — statement only

This file sets up the problem and nothing more.  The conjecture below is stated
precisely and is currently proved by `sorry`, so Lean reports it as open: the
build succeeds, the open goal raises `declaration uses 'sorry'`, and
`#print axioms` exposes `sorryAx`.  That is the honest state of affairs, and it
is what any future progress has to remove.

## Main definitions

* `CollatzProof.C` — the classical map, `n ↦ n / 2` on evens and `n ↦ 3n + 1`
  on odds.
* `CollatzProof.T` — the Terras accelerated map, which folds the forced halving
  after an odd step into that step: `n ↦ (3n + 1) / 2` on odds.

## Main statements

* `CollatzProof.collatz_conjecture` — every positive integer reaches `1` under
  iteration of `C`.  **Open**, and the only hole in the whole development.

The Terras form of the conjecture is *not* stated here.  It is a corollary, and
lives in `CollatzProof.Equivalence` next to the proof that the two formulations
agree.

## References

Terras, *A stopping time problem on the positive integers*, Acta Arith. 30
(1976), 241–252.
-/

namespace CollatzProof

/-- The classical Collatz map: `n / 2` when `n` is even, `3n + 1` when `n` is
odd.  Note `C 1 = 4`, so the orbit of `1` is the cycle `1 → 4 → 2 → 1`. -/
def C (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The Terras accelerated map: `n / 2` when `n` is even, `(3n + 1) / 2` when
`n` is odd.  The extra halving is free, since `3n + 1` is even for odd `n`.
This is the map for which the stopping time question is usually posed. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

section Sanity

/-- `3 → 10 → 5 → 16 → 8 → 4 → 2 → 1` under the classical map. -/
example : C^[7] 3 = 1 := by decide

/-- `3 → 5 → 8 → 4 → 2 → 1` under the Terras map, two steps shorter. -/
example : T^[5] 3 = 1 := by decide

/-- `1` is *not* a fixed point of `T`: the accelerated map sends `1 ↦ 2 ↦ 1`,
so the terminal cycle has length two rather than three. -/
example : T 1 = 2 ∧ T 2 = 1 := by decide

end Sanity

/-- **The Collatz conjecture.**  Every positive integer reaches `1` under
iteration of the classical map `C`.

This is open.  The proof below is `sorry`; replacing it is the whole point of
this project. -/
theorem collatz_conjecture (n : ℕ) (hn : 0 < n) : ∃ k, C^[k] n = 1 := by
  sorry

end CollatzProof

-- Confirmation that the main goal really is open: `sorryAx` appears.
#print axioms CollatzProof.collatz_conjecture
