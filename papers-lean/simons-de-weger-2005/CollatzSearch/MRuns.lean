import CollatzSearch.LMN
import CollatzSearch.RunGrowth

/-!
# The conditional m-run ladder (Simons–de Weger m-cycle method, finite instance)

**CLASSICAL.** The Simons–de Weger (2005) m-cycle method, cf. Hercher 2023
(arXiv:2201.00406), who reach `m ≤ 68` (Simons–de Weger) and `m ≤ 91` (Hercher) using verified
ranges of `2^60` and more.  Here only `2^24` is verified, so the results are much weaker.
**NOT progress on `no_nontrivial_cycles`**, which remains open: nothing here bounds the number
of odd runs of a general cycle.

* Lower bound on `k` (Farey): `farey_runs_190537`: with the Farey pair
  `125743/79335 > log₂3 > 176251/111202` (det 1), no `0 < K < 190537`, `3^K < 2^L`,
  `X ≥ 2^24`, `r ≤ 61` satisfies `2^L X^r ≤ 3^K (X+1)^r` (kernel certificate at `r = 61`,
  false at `r = 62`).
* Upper bound on `k` (`runs_bound_of_min`, `RunGrowth.lean`): `5^r k ≤ 5 (s+t) W r`.
* `state_of_the_art_runs` (**unconditional, finite-range instance**): the odd cycle minimum `m`
  from `state_of_the_art` has (`≥ 18` odd runs or `k ≥ 225644606`) and
  (`≥ 62` odd runs or `k ≥ 190537`), for the window `L` produced by `state_of_the_art`.
  Per lap: `state_of_the_art_runs_minimalPeriod` (RunsWindow.lean, `Mod3`/`RunsWindow`) proves the same
  bounds for every period of `m`, in particular `L = Function.minimalPeriod T m`, so no
  nontrivial cycle has, per lap, `≤ 17` odd runs and `k < 225,644,606` odd steps.
* `state_of_the_art_runs_of_LMN` (**CONDITIONAL on the unformalized `LMNHyp`**, vacuous if the
  transcription is false): the same `m` has `≥ 14` odd runs.  Named instances `…_of_Laurent08`
  `(25.2, 0.21, 20)` and `…_of_LMN95` `(24.34, 0.14, 21)` (see `LMN.lean` for provenance).

`oddRuns L m` counts even→odd transitions in the window `L`.  The primary reference for these
bounds is now `state_of_the_art_runs_minimalPeriod` (RunsWindow.lean, `Mod3`/`RunsWindow`), which states
them per lap, for `L = Function.minimalPeriod T m`.
-/

namespace CollatzSearch
open CollatzProof

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

/-- **Unconditional, finite-range instance of the Simons–de Weger m-cycle theorem
(classical).** A positive `C`-cycle point `n ∉ {1,2,4}` yields the odd `T`-orbit minimum `m`,
`2^24 ≤ m ≤ n`, period `L > 0`, `k = S_L(m) ≥ 12276`, with (`oddRuns L m ≥ 18` or
`k ≥ 225644606`) and (`oddRuns L m ≥ 62` or `k ≥ 190537`).  Not Goal progress. -/
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

/-- **CONDITIONAL on `LMNHyp`** (an unformalized transcription of LMN 1995 / Laurent 2008;
vacuous if the transcription is false): the conclusion of `state_of_the_art_runs` plus
`oddRuns L m ≥ 14`.  Classical method (Simons–de Weger 2005); not Goal progress. -/
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

/-- Instance, **CONDITIONAL** on `LMNHyp 25.2 0.21 20` (Laurent 2008 Cor. 1, `m = 20`;
corroborated by a secondary source only, see `LMN.lean`). -/
theorem state_of_the_art_runs_of_Laurent08 (H : LMNHyp 25.2 0.21 20)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      12276 ≤ oddSteps L m ∧
      (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
      (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) ∧ 14 ≤ oddRuns L m :=
  state_of_the_art_runs_of_LMN (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) H n hn ℓ hℓ h hne

/-- Instance, **CONDITIONAL** on `LMNHyp 24.34 0.14 21` (LMN 1995 constants from memory,
unverified). -/
theorem state_of_the_art_runs_of_LMN95 (H : LMNHyp 24.34 0.14 21)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      12276 ≤ oddSteps L m ∧
      (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
      (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) ∧ 14 ≤ oddRuns L m :=
  state_of_the_art_runs_of_LMN (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) H n hn ℓ hℓ h hne

end CollatzSearch

#print axioms CollatzSearch.certR_above
#print axioms CollatzSearch.certR_below
#print axioms CollatzSearch.certR_runs
#print axioms CollatzSearch.farey_runs_190537
#print axioms CollatzSearch.growth_runs
#print axioms CollatzSearch.W_small
#print axioms CollatzSearch.W_small13
#print axioms CollatzSearch.state_of_the_art_runs
#print axioms CollatzSearch.state_of_the_art_runs_of_LMN
#print axioms CollatzSearch.state_of_the_art_runs_of_Laurent08
#print axioms CollatzSearch.state_of_the_art_runs_of_LMN95
#print axioms CollatzSearch.certR_runs_not_le
