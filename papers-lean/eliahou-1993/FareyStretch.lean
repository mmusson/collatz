/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Farey

/-!
# A uniform gap for `2^L − 3^k` up to `k = 225644606`

This file applies the method of `Farey` to the Farey pair
`272500658/171928773 > log₂ 3 > 85137581/53715833` (with determinant `1`; both fractions are
convergents of `log₂ 3`), which gives `GapBelow 225644606 30`. The kernel certificates are stated
with powers split as `b^(na + r) = (replicate n (b^a)).prod · b^r` (`pow_split`), since the
kernel refuses a single `Nat.pow` whose result has more than about `2^24` bits. The largest
numbers have about `3.6 · 10^8` bits.

Consequently, a nontrivial positive `T`-cycle (at any phase, for any period) with at most two odd
runs has at least `225644606` odd steps and length at least `357638240`. The last section reduces
`LinFormHyp` to the range `k ≥ 225644606`; results there assume `LinFormHyp 225644606 c μ`, which
is not proved here.

## Main results

- `gapBelow_225644606`: `GapBelow 225644606 30`.
- `few_runs_cycle_trivial_farey2`: a positive `T`-cycle point with at most two odd runs and fewer
  than `225644606` odd steps is `1` or `2`.
- `one_circuit_eq_one_farey2`, `two_circuit_eq_one_farey2`: 1- and 2-circuits with fewer than
  `225644606` odd steps are trivial.
- `nontrivial_C_cycle_three_runs_farey2`: the corresponding statement for `C`-cycles.
- `linFormHyp_of_tail2`: `LinFormHyp 225644606 c μ` implies `LinFormHyp 100000 c μ` for `c ≥ 30`.

## References

- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
- J. L. Simons, B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the
  3n+1 problem*, Acta Arith. 117 (2005), 51–70.
-/

namespace Collatz

open CollatzProof

/-! ### Kernel certificates -/

/-- Splitting a power into a product of `n` equal pieces times a remainder. -/
theorem pow_split (b n a r : ℕ) : b^(n*a + r) = (List.replicate n (b^a)).prod * b^r := by
  rw [List.prod_replicate, pow_add, ← pow_mul, mul_comm n a]

/-- The Farey determinant of the pair. -/
theorem cert2_det : 272500658 * 53715833 = 85137581 * 171928773 + 1 := by norm_num

theorem cert2_above_split :
    ((List.replicate 40 (3^4298219)).prod * 3^13) <
      ((List.replicate 40 (2^6812516)).prod * 2^18) := by
  decide +kernel

theorem cert2_gap_split :
    ((List.replicate 40 (2^6812516)).prod * 2^18) ≤
      2^30 * (((List.replicate 40 (2^6812516)).prod * 2^18) -
        ((List.replicate 40 (3^4298219)).prod * 3^13)) := by
  decide +kernel

theorem cert2_below_split :
    ((List.replicate 16 (2^5321098)).prod * 2^13) <
      ((List.replicate 16 (3^3357239)).prod * 3^9) := by
  decide +kernel

theorem cert2_period_split :
    ((List.replicate 48 (2^7450796)).prod * 2^31) <
      ((List.replicate 48 (3^4700929)).prod * 3^14) := by
  decide +kernel

/-- `3^171928773 < 2^272500658`. -/
theorem cert2_above : 3^171928773 < 2^272500658 := by
  rw [show 171928773 = 40 * 4298219 + 13 from rfl, show 272500658 = 40 * 6812516 + 18 from rfl,
    pow_split, pow_split]; exact cert2_above_split

/-- `2^272500658 ≤ 2^30 (2^272500658 − 3^171928773)`. -/
theorem cert2_gap : 2^272500658 ≤ 2^30 * (2^272500658 - 3^171928773) := by
  rw [show 171928773 = 40 * 4298219 + 13 from rfl, show 272500658 = 40 * 6812516 + 18 from rfl,
    pow_split, pow_split]; exact cert2_gap_split

/-- `2^85137581 < 3^53715833`. -/
theorem cert2_below : 2^85137581 < 3^53715833 := by
  rw [show 53715833 = 16 * 3357239 + 9 from rfl, show 85137581 = 16 * 5321098 + 13 from rfl,
    pow_split, pow_split]; exact cert2_below_split

/-- `2^357638239 < 3^225644606`. -/
theorem cert2_period : 2^357638239 < 3^225644606 := by
  rw [show 357638239 = 48 * 7450796 + 31 from rfl, show 225644606 = 48 * 4700929 + 14 from rfl,
    pow_split, pow_split]; exact cert2_period_split

/-! ### The gap and its consequences -/

/-- `GapBelow 225644606 30`. -/
theorem gapBelow_225644606 : GapBelow 225644606 30 :=
  gapBelow_of_farey cert2_det cert2_above cert2_below cert2_gap

/-- A positive `T`-cycle point `x` (at any phase, for any period `L > 0`) whose window has at most
two odd runs and fewer than `225644606` odd steps is `1` or `2`. -/
theorem few_runs_cycle_trivial_farey2 {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < 225644606) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_gap gapBelow_225644606 hx hL hc hr hk

/-- Every 1-circuit with `k < 225644606` has `m = 1`. -/
theorem one_circuit_eq_one_farey2 {m k l : ℕ} (h : IsOneCircuit m k l) (hk : k < 225644606) :
    m = 1 :=
  one_circuit_eq_one_of_gap gapBelow_225644606 h hk

/-- Every 2-circuit with `k1 + k2 < 225644606` has `m = 1`. -/
theorem two_circuit_eq_one_farey2 {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2)
    (hk : k1 + k2 < 225644606) : m = 1 :=
  two_circuit_eq_one_of_gap gapBelow_225644606 h hk

/-- A nontrivial positive `C`-cycle point `n` yields an odd `T`-cycle point `m` with
`2^17 ≤ m ≤ n` whose window either has at least three odd runs, or has at least `225644606` odd
steps and length `L ≥ 357638240`; it also satisfies the bounds of `nontrivial_C_cycle_runs`. -/
theorem nontrivial_C_cycle_three_runs_farey2 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) ∧
      ((225644606 ≤ oddSteps L m ∧ 357638239 < L) ∨ 3 ≤ oddRuns L m) :=
  nontrivial_C_cycle_three_runs_of_gap gapBelow_225644606 cert2_period n hn ℓ hℓ h h1 h2 h4

/-! ### `LinFormHyp` for `k ≥ 225644606` suffices -/

/-- For `c ≥ 30`, `LinFormHyp 225644606 c μ` implies `LinFormHyp 100000 c μ`. -/
theorem linFormHyp_of_tail2 {c μ : ℕ} (hc : 30 ≤ c) (H : LinFormHyp 225644606 c μ) :
    LinFormHyp 100000 c μ := linFormHyp_of_tail_gap gapBelow_225644606 hc H

/-- Under `LinFormHyp 225644606 100 14`, every positive `T`-cycle point with at most two odd runs
is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail2 (H : LinFormHyp 225644606 100 14) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm_tail_gap gapBelow_225644606 (by norm_num) H hx hL hc hr

/-- Under `LinFormHyp 225644606 100 14`, every nontrivial `C`-cycle yields a `T`-cycle point
`m ≥ 2^17` whose window has at least three odd runs. -/
theorem nontrivial_C_cycle_three_runs_of_linForm_tail2 (H : LinFormHyp 225644606 100 14)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 3 ≤ oddRuns L m :=
  nontrivial_C_cycle_three_runs_of_linForm_tail_gap gapBelow_225644606 (by norm_num) H
    n hn ℓ hℓ h h1 h2 h4

end Collatz
