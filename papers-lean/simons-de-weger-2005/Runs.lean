/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import OneCircuit
import Collatz.CycleMin

/-!
# The odd-run inequality for cycles

In this file we prove the Simons–de Weger inequality for cycles of the Terras map `T`: if every
point of a `T`-cycle of length `L` with `k` odd steps is at least `X`, and the cycle has `r` odd
runs, then `2^L X^r ≤ 3^k (X+1)^r`, i.e. `0 < L log 2 − k log 3 ≤ r log(1 + 1/X)`. The proof uses
the exact weight `wt x = x + (x mod 2)`, which telescopes along the orbit.

The run count `oddRuns L x` counts even→odd transitions along any presentation of the cycle, so
the inequality does not depend on the starting point. When `L` is the minimal period and the
cycle contains both parities, `oddRuns L x` is the number of maximal cyclic odd runs; for a period
`L = t·p` it is `t` times larger (`oddRuns_mul` in `RunsRotate`).

## Main definitions

- `wt x`: the weight `x + (x mod 2)`, equal to `x + 1` for odd `x` and to `x` for even `x`.
- `runStart x`: `1` if `x` is even and `T x` is odd, and `0` otherwise.
- `oddRuns j n`: the number of even→odd transitions among the steps `n → T n → ⋯ → T^j n`.

## Main results

- `run_step`: if `X ≤ T x`, then `2·wt(T x)·X^e ≤ 3^{x mod 2}·wt(x)·(X+1)^e`, `e = runStart x`.
- `run_orbit`: if `X ≤ T^i n` for `1 ≤ i ≤ j`, then
  `2^j·wt(T^j n)·X^r ≤ 3^{S_j(n)}·wt(n)·(X+1)^r` with `r = oddRuns j n`.
- `cycle_run_ineq`: for a `T`-cycle `T^L x = x`, `x > 0`, all of whose points are at least `X`,
  `2^L X^r ≤ 3^k (X+1)^r` with `k = S_L(x)` and `r = oddRuns L x`.
- `oddRuns_le_oddSteps_of_cycle`: on a cycle, `oddRuns L x ≤ S_L(x)`.

## Notation

`S_j(n) = oddSteps j n` is the number of odd steps among `n, T n, …, T^{j-1} n`.

## References

- J. L. Simons, B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the
  3n+1-problem*, Acta Arith. 117 (2005), 51–70.
-/

namespace Collatz
open CollatzProof

/-! ### Weights and run starts -/

/-- The weight `wt x = x + (x mod 2)`: `x + 1` on odd `x`, `x` on even `x`. -/
def wt (x : ℕ) : ℕ := x + x % 2

/-- `runStart x = 1` iff `x` is even and `T x` is odd (the start of an odd run), else `0`. -/
def runStart (x : ℕ) : ℕ := if x % 2 = 0 ∧ T x % 2 = 1 then 1 else 0

/-- `oddRuns j n` is the number of even→odd transitions `T^i n → T^{i+1} n` with `i < j`. -/
def oddRuns : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j+1, n => oddRuns j (T n) + runStart n

/-! ### The run inequality -/

/-- One step of the run inequality: if `X ≤ T x`, then
`2·wt(T x)·X^e ≤ 3^{x mod 2}·wt(x)·(X+1)^e` with `e = runStart x`. -/
theorem run_step (X x : ℕ) (hX : X ≤ T x) :
    2 * wt (T x) * X ^ runStart x ≤ 3 ^ (x % 2) * wt x * (X+1) ^ runStart x := by
  unfold runStart wt
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (T x) with hy | hy
  · have := two_mul_T_even hx
    rw [if_neg (by omega), hx, hy]; simp only [pow_zero]; omega
  · have := two_mul_T_even hx
    rw [if_pos (by omega), hx, hy]; simp only [pow_zero, pow_one]
    nlinarith
  · have := two_mul_T_odd hx
    rw [if_neg (by omega), hx, hy]; simp only [pow_zero, pow_one]; omega
  · have := two_mul_T_odd hx
    rw [if_neg (by omega), hx, hy]; simp only [pow_zero, pow_one]; omega

/-- The run inequality along an orbit: if `X ≤ T^i n` for `1 ≤ i ≤ j`, then
`2^j·wt(T^j n)·X^r ≤ 3^{S_j(n)}·wt(n)·(X+1)^r` with `r = oddRuns j n`. -/
theorem run_orbit (j : ℕ) : ∀ (n X : ℕ), (∀ i, 1 ≤ i → i ≤ j → X ≤ T^[i] n) →
    2^j * wt (T^[j] n) * X ^ oddRuns j n ≤
      3 ^ oddSteps j n * wt n * (X+1) ^ oddRuns j n := by
  induction j with
  | zero => intro n X _; simp [oddRuns, oddSteps]
  | succ j ih =>
    intro n X h
    have hIH := ih (T n) X (fun i h1 h2 ↦ by
      have := h (i+1) (by omega) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have hs := run_step X n (by simpa using h 1 le_rfl (by omega))
    rw [Function.iterate_succ_apply]
    simp only [oddRuns, oddSteps, pow_add, pow_succ]
    set A := 2^j * wt (T^[j] (T n)) * X ^ oddRuns j (T n)
    set B := 3 ^ oddSteps j (T n) * wt (T n) * (X+1) ^ oddRuns j (T n)
    calc 2 ^ j * 2 * wt (T^[j] (T n)) * (X ^ oddRuns j (T n) * X ^ runStart n)
        = A * (2 * X ^ runStart n) := by simp only [A]; ring
      _ ≤ B * (2 * X ^ runStart n) := Nat.mul_le_mul_right _ hIH
      _ = 3 ^ oddSteps j (T n) * (X+1) ^ oddRuns j (T n) *
            (2 * wt (T n) * X ^ runStart n) := by
          simp only [B]; ring
      _ ≤ 3 ^ oddSteps j (T n) * (X+1) ^ oddRuns j (T n) *
            (3 ^ (n % 2) * wt n * (X+1) ^ runStart n) := Nat.mul_le_mul_left _ hs
      _ = 3 ^ oddSteps j (T n) * 3 ^ (n % 2) * wt n *
            ((X + 1) ^ oddRuns j (T n) * (X + 1) ^ runStart n) := by ring

/-- **Cycle run inequality** (Simons–de Weger). If `x > 0`, `T^L x = x` and every point of the
cycle is at least `X`, then `2^L X^r ≤ 3^k (X+1)^r` with `k = S_L(x)` and `r = oddRuns L x`. -/
theorem cycle_run_ineq {x L X : ℕ} (hx : 0 < x) (hc : T^[L] x = x) (hX : ∀ i, X ≤ T^[i] x) :
    2^L * X ^ oddRuns L x ≤ 3 ^ oddSteps L x * (X+1) ^ oddRuns L x := by
  have h := run_orbit L x X (fun i _ _ ↦ hX i)
  rw [hc] at h
  have hw : 0 < wt x := by unfold wt; omega
  have h' : (2^L * X ^ oddRuns L x) * wt x ≤
      (3 ^ oddSteps L x * (X+1) ^ oddRuns L x) * wt x := by
    calc (2^L * X ^ oddRuns L x) * wt x = 2^L * wt x * X ^ oddRuns L x := by ring
      _ ≤ 3 ^ oddSteps L x * wt x * (X+1) ^ oddRuns L x := h
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h' hw

/-! ### Runs and odd steps -/

/-- A run start is followed by an odd point: `runStart n ≤ (T n) mod 2`. -/
theorem runStart_le (n : ℕ) : runStart n ≤ T n % 2 := by
  unfold runStart; split_ifs with h <;> omega

/-- The number of runs is at most the number of odd steps of the shifted orbit. -/
theorem oddRuns_le (j : ℕ) : ∀ n, oddRuns j n ≤ oddSteps j (T n) := by
  induction j with
  | zero => intro n; simp [oddRuns]
  | succ j ih =>
    intro n
    have := ih (T n); have := runStart_le n
    simp only [oddRuns, oddSteps]; omega

/-- On a cycle `T^L x = x`, the number of odd runs is at most the number of odd steps. -/
theorem oddRuns_le_oddSteps_of_cycle {x L : ℕ} (hc : T^[L] x = x) :
    oddRuns L x ≤ oddSteps L x := by
  have h1 := oddRuns_le L x
  have h2 := oddSteps_cycle_invariant hc 1
  simp only [Function.iterate_one] at h2
  omega

/-- The trivial cycle `1 → 2 → 1` has one odd run. -/
theorem oddRuns_two_one : oddRuns 2 1 = 1 := by decide

/-! ### Examples -/

-- The cycle inequality at the trivial cycle `x = 1`, `L = 2`, `X = 1` reads `4 ≤ 6`.
example : 2^2 * 1^(oddRuns 2 1) ≤ 3^(oddSteps 2 1) * (1+1)^(oddRuns 2 1) := by decide

end Collatz
