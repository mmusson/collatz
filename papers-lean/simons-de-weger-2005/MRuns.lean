/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import LMN
import RunGrowth

/-!
# Lower bounds on the number of odd runs of a cycle

In this file we run the Simons–de Weger `m`-cycle method with the verified range `2^24`. A Farey
pair for `log₂ 3` and the cycle run inequality give a lower bound on the number `k` of odd steps
of a cycle with few odd runs; the run growth bound `runs_bound_of_min` of `RunGrowth` gives an
upper bound on `k`. Together they show that the odd minimum `m` of a nontrivial cycle has at least
`18` odd runs or at least `225644606` odd steps, and at least `62` odd runs or at least `190537`
odd steps, in the window `L` produced by `state_of_the_art`. Per-lap versions, valid for every
period of `m`, are in `RunsWindow`.

Simons and de Weger reach `m ≤ 68` and Hercher `m ≤ 91` using much larger verified ranges; the
bounds here are correspondingly weaker. Nothing here bounds the number of odd runs of a general
cycle.

The results `state_of_the_art_runs_of_LMN`, `state_of_the_art_runs_of_Laurent08` and
`state_of_the_art_runs_of_LMN95` assume the hypothesis `LMNHyp` of `LMN` (an explicit lower bound
for linear forms in two logarithms), which is not proved here. Under it, the same `m` has at least
`14` odd runs.

## Main results

- `farey_runs_190537`: with the Farey pair `125743/79335 > log₂ 3 > 176251/111202`, no
  `0 < K < 190537`, `3^K < 2^L`, `X ≥ 2^24`, `r ≤ 61` satisfies `2^L X^r ≤ 3^K (X+1)^r`.
- `state_of_the_art_runs`: the odd cycle minimum `m` from `state_of_the_art` has at least `18` odd
  runs or `k ≥ 225644606`, and at least `62` odd runs or `k ≥ 190537`.
- `state_of_the_art_runs_of_LMN`: under `LMNHyp`, the same `m` also has at least `14` odd runs.

## References

- J. L. Simons, B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the
  3n+1-problem*, Acta Arith. 117 (2005), 51–70.
- C. Hercher, *There are no Collatz m-cycles with m ≤ 91*, J. Integer Seq. 26 (2023),
  Art. 23.3.5.
- M. Laurent, M. Mignotte, Yu. Nesterenko, *Formes linéaires en deux logarithmes et déterminants
  d'interpolation*, J. Number Theory 55 (1995), 285–321.
- M. Laurent, *Linear forms in two logarithms and interpolation determinants II*, Acta Arith. 133
  (2008), 325–348.
-/

namespace Collatz
open CollatzProof

/-! ### A Farey certificate -/

/-- Determinant of the Farey pair `125743/79335`, `176251/111202`. -/
theorem certR_det : 125743 * 111202 = 176251 * 79335 + 1 := by norm_num
/-- `3^79335 < 2^125743` (kernel). -/
theorem certR_above : 3^79335 < 2^125743 := by decide +kernel
/-- `2^176251 < 3^111202` (kernel). -/
theorem certR_below : 2^176251 < 3^111202 := by decide +kernel
/-- `3^79335 (2^24+1)^61 < 2^125743 (2^24)^61` (kernel; false with 62 in place of 61). -/
theorem certR_runs : 3^79335 * (2^24 + 1)^61 < 2^125743 * (2^24)^61 := by decide +kernel
/-- Negated form of `certR_runs`, named so that it can be applied without re-elaboration. -/
theorem certR_runs_not_le : ¬ (2^125743 * (2^24:ℕ)^61 ≤ 3^79335 * (2^24 + 1)^61) :=
  Nat.not_le_of_lt certR_runs

/-- **Farey lower bound for few runs.** If `0 < K < 190537`, `3^K < 2^L`, `2^24 ≤ X`,
`r ≤ 61` and `2^L X^r ≤ 3^K (X+1)^r`, then `False`. -/
theorem farey_runs_190537 {K L X r : ℕ} (hK0 : 0 < K) (hK : K < 190537) (h3 : 3^K < 2^L)
    (hX : 2^24 ≤ X) (hr : r ≤ 61) (h : 2^L * X^r ≤ 3^K * (X+1)^r) : False := by
  have fb := farey_bound certR_det certR_above certR_below hK0 (by norm_num; exact hK) h3
  set p := 125743 with hp
  set q := 79335 with hq
  set X0 : ℕ := 2^24 with hX0
  -- 2^p X^r ≤ 3^q (X+1)^r
  have s1 : 2^p * X^r ≤ 3^q * (X+1)^r := by
    clear_value p q
    have : 3^K * (2^p * X^r) ≤ 3^K * (3^q * (X+1)^r) := by
      calc 3^K * (2^p * X^r) = (3^K * 2^p) * X^r := by ring
        _ ≤ (3^q * 2^L) * X^r := Nat.mul_le_mul_right _ fb
        _ = 3^q * (2^L * X^r) := by ring
        _ ≤ 3^q * (3^K * (X+1)^r) := Nat.mul_le_mul_left _ h
        _ = 3^K * (3^q * (X+1)^r) := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  -- reduce to X0
  have s2 : 2^p * X0^r ≤ 3^q * (X0+1)^r := by
    clear_value p q
    have hmono : X0 * (X+1) ≤ X * (X0+1) := by nlinarith
    have : (X+1)^r * (2^p * X0^r) ≤ (X+1)^r * (3^q * (X0+1)^r) := by
      calc (X+1)^r * (2^p * X0^r) = 2^p * (X0 * (X+1))^r := by rw [mul_pow]; ring
        _ ≤ 2^p * (X * (X0+1))^r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmono r)
        _ = (2^p * X^r) * (X0+1)^r := by rw [mul_pow]; ring
        _ ≤ (3^q * (X+1)^r) * (X0+1)^r := Nat.mul_le_mul_right _ s1
        _ = (X+1)^r * (3^q * (X0+1)^r) := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  -- reduce to r = 61
  have s3 : 2^p * X0^61 ≤ 3^q * (X0+1)^61 := by
    clear_value p q
    obtain ⟨d, hd⟩ : ∃ d, 61 = r + d := ⟨61 - r, by omega⟩
    rw [hd, pow_add, pow_add]
    calc 2^p * (X0^r * X0^d) = (2^p * X0^r) * X0^d := by ring
      _ ≤ (3^q * (X0+1)^r) * (X0+1)^d :=
          Nat.mul_le_mul s2 (Nat.pow_le_pow_left (Nat.le_succ _) d)
      _ = 3^q * ((X0+1)^r * (X0+1)^d) := by rw [mul_assoc]
  rw [hp, hq, hX0] at s3
  exact certR_runs_not_le s3

/-! ### Numerical lemmas -/

/-- `749 (5 + 51 (l+21)²) < 2^l` for `l ≥ 27`. -/
theorem growth_runs (l : ℕ) (hl : 27 ≤ l) : 749 * (5 + 51 * (l + 21)^2) < 2^l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : (n+1+21)^2 ≤ 2*(n+21)^2 := by nlinarith
    rw [pow_succ 2 n]; nlinarith

/-- `175 W r < 190537·5^r` for `1 ≤ r ≤ 17` (fails at `r = 18`). -/
theorem W_small (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ 17) : 175 * W r < 190537 * 5^r := by
  interval_cases r <;> simp [W]

/-- `5 W r ≤ 749·5^r` for `1 ≤ r ≤ 13` (fails at `r = 14`). -/
theorem W_small13 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ 13) : 5 * W r ≤ 749 * 5^r := by
  interval_cases r <;> simp [W]

/-! ### Bounds on the number of odd runs -/

/-- **Simons–de Weger bound with verified range `2^24`.** A positive `C`-cycle point
`n ∉ {1, 2, 4}` yields the odd `T`-orbit minimum `m` with `2^24 ≤ m ≤ n`, a period `L > 0` and
`k = S_L(m) ≥ 12276`, such that `oddRuns L m ≥ 18` or `k ≥ 225644606`, and `oddRuns L m ≥ 62` or
`k ≥ 190537`. -/
theorem state_of_the_art_runs (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      12276 ≤ oddSteps L m ∧
      (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
      (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) := by
  obtain ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, -, -, -, -, hk', -, -⟩ :=
    state_of_the_art n hn ℓ hℓ h hne
  have h24 : (16777216 : ℕ) ≤ m := by norm_num at h2; exact h2
  have hm0 : 0 < m := by omega
  have h3k := three_pow_lt_two_pow_of_cycle hm0 h4 h5
  have hineq := cycle_run_ineq hm0 h5 h6
  have hr1 := oddRuns_pos_of_cycle hm0 h4 h5
  have hsec : 62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m := by
    by_contra hc
    push Not at hc
    exact farey_runs_190537 (by omega) hc.2 h3k h2 (by omega) hineq
  refine ⟨m, L, h1, h2, h3, h4, h5, h6, hk', ?_, hsec⟩
  by_contra hc
  push Not at hc
  have hk2 : 190537 ≤ oddSteps L m := by omega
  have gap := gapBelow_225644606 _ L (by omega) hc.2 h3k
  have rb := runs_bound_of_min (t := 5) h1 h4 h5 h6 h3k gap
    (le_trans (by omega : oddRuns L m ≤ 32) (by norm_num))
  have hw := W_small _ hr1 (by omega)
  generalize oddRuns L m = r at rb hw
  generalize oddSteps L m = k at rb hk2
  have : 5^r * 190537 ≤ 5^r * k := Nat.mul_le_mul_left _ hk2
  omega

/-! ### Bounds assuming a lower bound for linear forms in two logarithms -/

/-- Assume `LMNHyp Cst c0 m0` with `0 ≤ Cst ≤ 51/2`, `c0 ≤ 1` and `0 ≤ m0 ≤ 21`. Then the
conclusion of `state_of_the_art_runs` holds together with `oddRuns L m ≥ 14`. -/
theorem state_of_the_art_runs_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2)
    (hc0 : c0 ≤ 1) (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      12276 ≤ oddSteps L m ∧
      (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
      (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) ∧ 14 ≤ oddRuns L m := by
  obtain ⟨m, L, h1, h2, h3, h4, h5, h6, hk', hA, hB⟩ := state_of_the_art_runs n hn ℓ hℓ h hne
  refine ⟨m, L, h1, h2, h3, h4, h5, h6, hk', hA, hB, ?_⟩
  by_contra hc
  push Not at hc
  have hm0' : 0 < m := by omega
  have h3k := three_pow_lt_two_pow_of_cycle hm0' h4 h5
  have hr1 := oddRuns_pos_of_cycle hm0' h4 h5
  have hk : 225644606 ≤ oddSteps L m := by omega
  have gap := gap_of_LMN hC0 hC hc0 hm0 hm1 H (by omega) h3k
  have rb := runs_bound_of_min (t := 4) h1 h4 h5 h6 h3k gap
    (le_trans (by omega : oddRuns L m ≤ 16) (by norm_num))
  have hw := W_small13 _ hr1 (by omega)
  have hl27 : 27 ≤ Nat.log 2 (oddSteps L m) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hpl : 2^(Nat.log 2 (oddSteps L m)) ≤ oddSteps L m := Nat.pow_log_le_self 2 (by omega)
  have hg := growth_runs _ hl27
  generalize Nat.log 2 (oddSteps L m) = l at hl27 hpl hg rb
  generalize oddRuns L m = r at rb hw
  generalize oddSteps L m = k at rb hpl
  set A := 5 + 51 * (l + 21)^2 with hA
  have hst : 1 + 51 * (l + 21)^2 + 4 = A := by omega
  rw [hst] at rb
  have hP : 0 < 5^r := by positivity
  have c1 : 5^r * k ≤ A * (749 * 5^r) := by
    calc 5^r * k ≤ 5 * A * W r := rb
      _ = A * (5 * W r) := by ring
      _ ≤ A * (749 * 5^r) := Nat.mul_le_mul_left _ hw
  have c2 : 5^r * (749 * A) < 5^r * 2^l := Nat.mul_lt_mul_of_pos_left hg hP
  have c3 : 5^r * 2^l ≤ 5^r * k := Nat.mul_le_mul_left _ hpl
  have : A * (749 * 5^r) = 5^r * (749 * A) := by ring
  omega

/-- `state_of_the_art_runs_of_LMN` under `LMNHyp 25.2 0.21 20`, the constants of Laurent
(2008, Cor. 1, `m = 20`). -/
theorem state_of_the_art_runs_of_Laurent08 (H : LMNHyp 25.2 0.21 20)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      12276 ≤ oddSteps L m ∧
      (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
      (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) ∧ 14 ≤ oddRuns L m :=
  state_of_the_art_runs_of_LMN (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) H n hn ℓ hℓ h hne

/-- `state_of_the_art_runs_of_LMN` under `LMNHyp 24.34 0.14 21`, the constants of
Laurent–Mignotte–Nesterenko (1995, Cor. 2). -/
theorem state_of_the_art_runs_of_LMN95 (H : LMNHyp 24.34 0.14 21)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      12276 ≤ oddSteps L m ∧
      (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
      (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) ∧ 14 ≤ oddRuns L m :=
  state_of_the_art_runs_of_LMN (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) H n hn ℓ hℓ h hne

end Collatz
