/-
Copyright (c) 2026 Mike Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Musson
-/
import CollatzProof.Statement

/-!
# Elementary facts about `C`, `T` and `S`

Everything here is parity bookkeeping, and everything here is actually proved.
The two lemmas that matter downstream are `T_eq_C_of_even` and
`T_eq_C_C_of_odd`, which say that a single `T`-step is one `C`-step or two, and
`C_ne_one_of_odd`, which says that the `C`-step skipped over by an odd
`T`-step never lands on `1`.  That last fact is the only content in the
equivalence proof; without it, compressing `C`-steps into `T`-steps could in
principle step over the target.

For the Syracuse map the analogous facts are `exists_iterate_T_eq_S` (one `S`-step
is a positive number of `T`-steps) and the statement, inside it, that the skipped
values are even and positive, hence never `1`.
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

/-- Halving with enough fuel follows the `T`-orbit. If `0 < x ≤ k`, then the
`T`-orbit of `x` reaches `oddPartAux k x` after some `j` steps, every value before
that is even and positive, and the result is odd. -/
theorem iterate_T_eq_oddPartAux :
    ∀ k x, 0 < x → x ≤ k →
      oddPartAux k x % 2 = 1 ∧
      ∃ j, T^[j] x = oddPartAux k x ∧ ∀ i < j, T^[i] x % 2 = 0 ∧ 0 < T^[i] x := by
  intro k
  induction k with
  | zero => intro x hx hk; omega
  | succ k ih =>
    intro x hx hk
    by_cases he : x % 2 = 0
    · -- `x` is even and positive: one halving step, then recurse on `x / 2`.
      have hx2 : 0 < x / 2 := by omega
      have hk2 : x / 2 ≤ k := by omega
      obtain ⟨hodd, j, hj, hint⟩ := ih (x / 2) hx2 hk2
      have hstep : oddPartAux (k + 1) x = oddPartAux k (x / 2) := by
        simp [oddPartAux, he, hx]
      refine ⟨hstep ▸ hodd, j + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, T_of_even he, hstep]; exact hj
      · intro i hi
        rcases i with _ | i
        · exact ⟨he, hx⟩
        · rw [Function.iterate_succ_apply, T_of_even he]
          exact hint i (by omega)
    · -- `x` is odd: nothing to strip.
      have hstep : oddPartAux (k + 1) x = x := by simp [oddPartAux, he]
      refine ⟨by rw [hstep]; omega, 0, by rw [hstep]; rfl, fun i hi => by omega⟩

/-- The `T`-orbit of `x > 0` reaches `oddPart x`, which is odd, by halving steps
through even, positive values. -/
theorem iterate_T_eq_oddPart {x : ℕ} (hx : 0 < x) :
    oddPart x % 2 = 1 ∧
      ∃ j, T^[j] x = oddPart x ∧ ∀ i < j, T^[i] x % 2 = 0 ∧ 0 < T^[i] x :=
  iterate_T_eq_oddPartAux x x hx le_rfl

/-- `S n` is odd (for every `n`, since `3n + 1 > 0`). -/
theorem S_odd (n : ℕ) : S n % 2 = 1 := (iterate_T_eq_oddPart (by omega)).1

/-- For odd `n`, `T n = T (3n + 1)`: both equal `(3n + 1) / 2`. -/
theorem T_eq_T_three_mul_add_one {n : ℕ} (h : n % 2 = 1) : T n = T (3 * n + 1) := by
  rw [T_of_odd h, T_of_even (even_three_mul_add_one h)]

/-- **One `S`-step is a positive number of `T`-steps.** For odd `n` there is
`e ≥ 1` with `T^[e] n = S n`, and every value strictly between (`0 < i < e`) is even
and positive, hence never `1`. -/
theorem exists_iterate_T_eq_S {n : ℕ} (h : n % 2 = 1) :
    ∃ e, 0 < e ∧ T^[e] n = S n ∧ ∀ i, 0 < i → i < e → T^[i] n % 2 = 0 ∧ 0 < T^[i] n := by
  obtain ⟨hodd, j, hj, hint⟩ := iterate_T_eq_oddPart (x := 3 * n + 1) (by omega)
  -- The orbits of `n` and `3n + 1` agree from step one on.
  have hagree : ∀ i, 0 < i → T^[i] n = T^[i] (3 * n + 1) := by
    intro i hi
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_eq_T_three_mul_add_one h]
  -- `j > 0`, because `3n + 1` is even while its odd part is odd.
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · have h3 := even_three_mul_add_one h
      simp only [Function.iterate_zero, id] at hj
      rw [← hj] at hodd; omega
    · exact hpos
  refine ⟨j, hj0, by rw [hagree j hj0]; exact hj, fun i hi hij => ?_⟩
  rw [hagree i hi]; exact hint i hij

end CollatzProof
