/-
Copyright (c) 2026 Mike Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Musson
-/
import CollatzProof.Statement

/-!
# Elementary facts about `C` and `T`

Everything here is parity bookkeeping, and everything here is actually proved.
The two lemmas that matter downstream are `T_eq_C_of_even` and
`T_eq_C_C_of_odd`, which say that a single `T`-step is one `C`-step or two, and
`C_ne_one_of_odd`, which says that the `C`-step skipped over by an odd
`T`-step never lands on `1`.  That last fact is the only content in the
equivalence proof; without it, compressing `C`-steps into `T`-steps could in
principle step over the target.
-/

namespace CollatzProof

/-- On even inputs the classical map halves. -/
theorem C_of_even {n : ℕ} (h : n % 2 = 0) : C n = n / 2 := by simp [C, h]

/-- On odd inputs the classical map is `3n + 1`. -/
theorem C_of_odd {n : ℕ} (h : n % 2 = 1) : C n = 3 * n + 1 := by simp [C, h]

/-- On even inputs the accelerated map halves. -/
theorem T_of_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by simp [T, h]

/-- On odd inputs the accelerated map is `(3n + 1) / 2`. -/
theorem T_of_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by simp [T, h]

/-- For odd `n` the value `3n + 1` is even, which is what makes the extra
halving in `T` legitimate. -/
theorem even_three_mul_add_one {n : ℕ} (h : n % 2 = 1) : (3 * n + 1) % 2 = 0 := by
  omega

/-- On evens, one `T`-step is exactly one `C`-step. -/
theorem T_eq_C_of_even {n : ℕ} (h : n % 2 = 0) : T n = C n := by
  rw [T_of_even h, C_of_even h]

/-- On odds, one `T`-step is exactly two `C`-steps. -/
theorem T_eq_C_C_of_odd {n : ℕ} (h : n % 2 = 1) : T n = C (C n) := by
  rw [C_of_odd h, C_of_even (even_three_mul_add_one h), T_of_odd h]

/-- The intermediate value skipped by an odd `T`-step is never `1`: for odd `n`
we have `C n = 3n + 1 ≥ 4`.  Note that `n % 2 = 1` already forces `n ≥ 1`, so no
positivity hypothesis is needed. -/
theorem C_ne_one_of_odd {n : ℕ} (h : n % 2 = 1) : C n ≠ 1 := by
  rw [C_of_odd h]; omega

/-- `0` is a fixed point of the classical map, so its orbit never reaches `1`. -/
theorem C_zero : C 0 = 0 := rfl

/-- `0` is a fixed point of the accelerated map too. -/
theorem T_zero : T 0 = 0 := rfl

/-- Two `C`-steps, written as an iterate. -/
theorem iterate_C_two (n : ℕ) : C^[2] n = C (C n) := rfl

/-- One `C`-step, written as an iterate. -/
theorem iterate_C_one (n : ℕ) : C^[1] n = C n := rfl

end CollatzProof
