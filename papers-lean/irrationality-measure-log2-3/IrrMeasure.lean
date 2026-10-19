/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import FareyStretch
import Collatz.StateOfArt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Irrationality measures of `log 3 / log 2` and cycles with few odd runs

In this file we define the hypothesis `IrrMeasHyp μ Q0`, an irrationality measure `μ` of
`log 3 / log 2` valid for denominators `q ≥ Q0`, and show that it implies the linear-form bound
`2^L ≤ 4 k^{μ-1} (2^L - 3^k)` for `k ≥ Q0` and `3^k < 2^L`. Combined with the gap estimate for
`k` below `225644606`, any polynomial irrationality measure with an explicit threshold
`Q0 ≤ 225644606` excludes nontrivial positive `T`-cycles with at most two odd runs, for every
number `k` of odd steps. This recovers the theorems of Steiner (one run) and Simons (two runs).

The hypothesis `IrrMeasHyp` is a definition, not an axiom; results that take it as a hypothesis
are conditional on it. An unconditional instance with `μ = 59` and `Q0 = 2^167` is proved in
`PadeCheb`; note that `IrrMeasHyp μ Q0` is false for every `μ` when `Q0 ≤ 1`.

## Main definitions

- `IrrMeasHyp μ Q0`: `|log 3 / log 2 - p/q| ≥ q^{-μ}` for all `p` and all `q ≥ max Q0 1`.

## Main results

- `linFormHyp_of_irrMeas`: `IrrMeasHyp μ Q0 → LinFormHyp Q0 2 (μ - 1)` for `μ, Q0 ≥ 1`.
- `linFormHyp_mono_c`, `linFormHyp_mono_K`: monotonicity of `LinFormHyp`.
- `few_runs_cycle_trivial_of_irrMeas`: if `IrrMeasHyp μ Q0` with `1 ≤ Q0 ≤ 225644606` and
  `8 (30 + 17 (μ - 1) + 2) ≤ 2^16`, every point of a positive `T`-cycle with at most two odd runs
  is `1` or `2`.
- `state_of_the_art_of_irrMeas`: under the same hypotheses, the minimal odd point of every
  nontrivial `C`-cycle has at least three odd runs, in addition to the known bounds.
- `not_irrMeasHyp_1_1`: `IrrMeasHyp 1 1` is false.

## References

- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
  Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
- Q. Wu, L. Wang, *On the irrationality measure of log 3*, J. Number Theory 142 (2014), 264–273.
  (This concerns `log 3`, not `log 3 / log 2`.)
- R. P. Steiner, *A theorem on the Syracuse problem*, Proc. 7th Manitoba Conf. Numer. Math.
  (1977), 553–559.
- J. L. Simons, *On the nonexistence of 2-cycles for the 3x+1 problem*, Math. Comp. 74 (2005),
  1565–1572.
-/
namespace Collatz
open CollatzProof

/-! ### The irrationality-measure hypothesis -/

/-- An irrationality measure `μ` of `log 3 / log 2` from `Q0` on: for all `p` and all `q ≥ Q0`
with `q ≥ 1`, `1/q^μ ≤ |log 3 / log 2 − p/q|`. This is false for every `μ` when `Q0 ≤ 1`. -/
def IrrMeasHyp (μ Q0 : ℕ) : Prop :=
  ∀ p q : ℕ, Q0 ≤ q → 0 < q → 1 / (q:ℝ)^μ ≤ |Real.log 3 / Real.log 2 - (p:ℝ)/q|

/-! ### From irrationality measures to linear forms -/

/-- An irrationality measure `μ ≥ 1` from `Q0 ≥ 1` gives the integer linear-form bound
`2^L ≤ 2^2 k^{μ−1} (2^L − 3^k)` for `k ≥ Q0`, `3^k < 2^L`. -/
theorem linFormHyp_of_irrMeas {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ : 1 ≤ Q0) (h : IrrMeasHyp μ Q0) :
    LinFormHyp Q0 2 (μ-1) := by
  intro k L hk hL
  have hk1 : 1 ≤ k := le_trans hQ hk
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0:ℝ) < k := by linarith
  set l2 := Real.log 2 with hl2def
  set l3 := Real.log 3 with hl3def
  have hl2 : 0 < l2 := Real.log_pos (by norm_num)
  have hl2' : 1/2 < l2 := by have := Real.log_two_gt_d9; linarith
  set A : ℝ := (2:ℝ)^L with hAdef
  set B : ℝ := (3:ℝ)^k with hBdef
  have hBpos : 0 < B := by positivity
  have hAB : B < A := by
    have : ((3^k:ℕ):ℝ) < ((2^L:ℕ):ℝ) := by exact_mod_cast hL
    push_cast at this; exact this
  have hlogA : Real.log A = L * l2 := Real.log_pow _ _
  have hlogB : Real.log B = k * l3 := Real.log_pow _ _
  have hlog : k * l3 < L * l2 := by
    rw [← hlogA, ← hlogB]; exact Real.log_lt_log hBpos hAB
  set t := L * l2 - k * l3 with htdef
  have htpos : 0 < t := by linarith
  have hexp : B * Real.exp t = A := by
    rw [htdef, Real.exp_sub, ← hlogA, ← hlogB, Real.exp_log hBpos,
      Real.exp_log (by linarith)]
    field_simp
  have h1t : B * (1 + t) ≤ A := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) hBpos.le
  -- irrationality measure
  have hi := h L k hk (by omega)
  have habs : |l3 / l2 - (L:ℝ) / k| = t / (k * l2) := by
    have : l3 / l2 - (L:ℝ) / k = -(t / (k * l2)) := by
      rw [htdef]; field_simp; ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
  rw [habs] at hi
  set K : ℝ := (k:ℝ)^(μ-1) with hKdef
  have hK1 : 1 ≤ K := one_le_pow₀ hkr
  have hkμ : (k:ℝ)^μ = k * K := by
    rw [hKdef, ← pow_succ']; congr 1; omega
  rw [hkμ, div_le_div_iff₀ (by positivity) (by positivity)] at hi
  have htK : l2 ≤ t * K := by nlinarith
  have hkey : 1 + t ≤ 4 * K * t := by
    rcases le_or_gt t 1 with h1 | h1 <;> nlinarith
  have hfin : A ≤ 4 * K * (A - B) := by
    have h2 : A * (1 + t) ≤ 4 * K * (A - B) * (1 + t) := by nlinarith
    exact le_of_mul_le_mul_right h2 (by linarith)
  have : ((2^L : ℕ) : ℝ) ≤ ((2^2 * k^(μ-1) * (2^L - 3^k) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hL.le]; push_cast
    rw [← hAdef, ← hBdef, ← hKdef]; linarith
  exact_mod_cast this

/-- `LinFormHyp` is monotone in the constant `c`. -/
theorem linFormHyp_mono_c {K0 c c' μ : ℕ} (hc : c ≤ c') (H : LinFormHyp K0 c μ) :
    LinFormHyp K0 c' μ := by
  intro k L hk hL
  calc 2^L ≤ 2^c * k^μ * (2^L - 3^k) := H k L hk hL
    _ ≤ 2^c' * k^μ * (2^L - 3^k) := by
      gcongr; norm_num

/-- `LinFormHyp` is monotone (upward) in the threshold `K0`. -/
theorem linFormHyp_mono_K {K0 K1 c μ : ℕ} (hK : K0 ≤ K1) (H : LinFormHyp K0 c μ) :
    LinFormHyp K1 c μ := fun k L hk hL => H k L (le_trans hK hk) hL

/-! ### Cycles with at most two odd runs -/

/-- Assume `IrrMeasHyp μ Q0` with `1 ≤ Q0 ≤ 225644606`, `μ ≥ 1` and
`8 (30 + 17 (μ−1) + 2) ≤ 2^16`. Then every point of a positive `T`-cycle with at most two odd
runs is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_irrMeas {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ1 : 1 ≤ Q0)
    (hQ : Q0 ≤ 225644606) (hside : 8 * (30 + 17 * (μ-1) + 2) ≤ 2^16) (h : IrrMeasHyp μ Q0)
    {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) :
    x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm_tail_gap gapBelow_225644606 hside
    (linFormHyp_mono_K hQ (linFormHyp_mono_c (by norm_num) (linFormHyp_of_irrMeas hμ hQ1 h)))
    hx hL hc hr

/-- Under the hypotheses of `few_runs_cycle_trivial_of_irrMeas`, the witness of
`state_of_the_art` for a nontrivial `C`-cycle also has at least three odd runs. -/
theorem state_of_the_art_of_irrMeas {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ1 : 1 ≤ Q0)
    (hQ : Q0 ≤ 225644606) (hside : 8 * (30 + 17 * (μ-1) + 2) ≤ 2^16) (H : IrrMeasHyp μ Q0)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L a b, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < a ∧ 0 < b ∧ oddSteps L m = 665*a + 11611*b ∧ L = 1054*a + 18403*b ∧
      12276 ≤ oddSteps L m ∧ 19457 ≤ L ∧ 3 ≤ oddRuns L m := by
  obtain ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL, hk', hL', -⟩ :=
    state_of_the_art n hn ℓ hℓ h hne
  refine ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL, hk', hL', ?_⟩
  have h24 : (16777216 : ℕ) ≤ m := by norm_num at h2; exact h2
  by_contra hcon
  rcases few_runs_cycle_trivial_of_irrMeas hμ hQ1 hQ hside H (x := m) (by omega) h4 h5
    (by omega) with e | e <;> omega

/-- The case `μ = 9`, `Q0 = 225644606` of `few_runs_cycle_trivial_of_irrMeas`. -/
theorem few_runs_cycle_trivial_of_irrMeas9 (H : IrrMeasHyp 9 225644606)
    {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) :
    x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_irrMeas (by norm_num) (by norm_num) le_rfl (by norm_num) H hx hL hc hr

/-! ### A false instance -/

/-- `IrrMeasHyp 1 1` is false, since `|log₂ 3 − 2| ≈ 0.415 < 1`. -/
theorem not_irrMeasHyp_1_1 : ¬ IrrMeasHyp 1 1 := by
  intro H
  have h := H 2 1 le_rfl one_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h34 : Real.log 3 < 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]; exact Real.log_lt_log (by norm_num) (by norm_num)
  have hr1 : 1 < Real.log 3 / Real.log 2 := by rw [one_lt_div hl2]; exact h23
  have hr2 : Real.log 3 / Real.log 2 < 2 := by rw [div_lt_iff₀ hl2]; linarith
  norm_num at h
  rw [abs_of_neg (by linarith)] at h
  linarith

/-! ### Examples -/

-- The side condition of `few_runs_cycle_trivial_of_irrMeas` holds for `μ = 9`.
example : 8 * (30 + 17 * (9-1) + 2) ≤ 2^16 := by norm_num

-- The linear-form bound of `linFormHyp_of_irrMeas` with `μ = 9` at `k = 5`, `L = 8`.
example : 2^8 ≤ 2^2 * 5^(9-1) * (2^8 - 3^5) := by norm_num

end Collatz
