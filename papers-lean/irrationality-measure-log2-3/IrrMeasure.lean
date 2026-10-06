import FareyStretch
import Collatz.StateOfArt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A polynomial irrationality measure of `log 3/log 2` excludes ≤ 2-run cycles (all `k`)

**CONDITIONAL on `IrrMeasHyp μ Q0` (unproved; definition, not axiom). NOT progress on
`no_nontrivial_cycles`.**

* `IrrMeasHyp μ Q0`: the standard literature form of an irrationality measure,
  `|log 3/log 2 − p/q| ≥ q^{−μ}` for all `p` and all `q ≥ max(Q0,1)`.
  Rhin 1987 gives `μ(log 3/log 2) ≤ 8.616` (believed; equivalently linear-form exponent
  `μ − 1 = 7.616`, the likely resolution of the 7.616/8.616 discrepancy in the log, UNVERIFIED);
  Wu–Wang 2014 give `≤ 5.125` (believed).  Whether a published result gives an explicit
  `Q0 ≤ 225644606` is UNVERIFIED.
  **`IrrMeasureReal` corrections (Gate 1).** (i) Provenance, secondary source only: Q. Wu, Math. Comp. 72
  (2003) 901–911 (DOI 10.1090/S0025-5718-02-01442-4), p. 902: Rhin "obtained a linear
  independence measure of 1, log2, log3 less than 7.616 ... it gives the best irrationality
  measure known of log3 (8.616)", i.e. Wu 2003 p. 902 quotes Rhin: `ν(1,log2,log3) < 7.616`
  and `μ(log 3) ≤ 8.616`.  Restricting to forms `q log3 − p log2` (constant coefficient 0)
  gives `μ(log3/log2) ≤ 8.616`, DERIVED here, not quoted, with a non-explicit threshold
  [`FareyBigCore`/`FareyBigCond` rewording].  Rhin's original (Springer, DOI 10.1007/978-1-4757-4267-1_11) not
  consulted.  (ii) It is stated with a NON-EXPLICIT threshold `H0(ε)`: the explicit threshold
  in `IrrMeasHyp 9 225644606` is unsupported by any located publication.  (iii) The Wu–Wang
  2014 figure `5.125` above is MISATTRIBUTED: that paper (J. Number Theory, DOI
  10.1016/j.jnt.2014.03.007, "On the irrationality measure of log 3") bounds `μ(log 3)`, not
  `μ(log 3/log 2)`.  (iv) `IrrMeasHyp μ Q0` is FALSE for every `μ` when `Q0 ≤ 1`
  (`IrrMeasureReal.not_irrMeasHyp_of_Q0_le_one`), so meaningful instances need `Q0 ≥ 2`.
* `linFormHyp_of_irrMeas`: `IrrMeasHyp μ Q0 → LinFormHyp Q0 2 (μ−1)` for `μ, Q0 ≥ 1`
  (real analysis: `1 − e^{−t} ≥ t/(1+t)` with `t = L log 2 − k log 3 ≥ log 2 / k^{μ−1}`).
* `few_runs_cycle_trivial_of_irrMeas`: if `1 ≤ Q0 ≤ 225644606` and `8(30 + 17(μ−1) + 2) ≤ 2^16`
  (i.e. `μ ≤ 481`), every positive `T`-cycle point with `≤ 2` odd runs is `1` or `2` — Steiner 1977
  (1-circuits) AND Simons 2005 (2-circuits), all `k`.
* `state_of_the_art_of_irrMeas`: C-level, every nontrivial `C`-cycle has `≥ 3` odd runs.
* `few_runs_cycle_trivial_of_irrMeas9`: named instance `IrrMeasHyp 9 225644606`.
* `not_irrMeasHyp_1_1`: sanity, `IrrMeasHyp 1 1` is FALSE (`p = 2, q = 1`).

**Correction of the `Closing` note.** The `Ellison`/`Closing` claim that 2-circuits need an exponential-type gap
`≈ 2^{−0.2075k}` "which no polynomial irrationality measure gives" is backwards: a polynomial
measure gives a relative gap `≳ k^{1−μ}`, far LARGER than `2^{−0.2075k}` for large `k`.  This file
proves that any polynomial measure (e.g. Rhin's, non-Baker) handles both 1- and 2-circuits; only
Ellison's EXPONENTIAL gap `e^{−L/10}` is too weak for 2-circuits.
-/
namespace Collatz
open CollatzProof

/-- **Unproved hypothesis (definition, not axiom)**: irrationality measure `μ` of `log 3/log 2`
from `Q0` on: for all `p` and `q ≥ Q0`, `q ≥ 1`, `1/q^μ ≤ |log 3/log 2 − p/q|`.
FALSE (so every theorem assuming it is vacuous) whenever `Q0 ≤ 1`, for every `μ`
(`IrrMeasureReal.not_irrMeasHyp_of_Q0_le_one`, `IrrMeasureReal`). -/
def IrrMeasHyp (μ Q0 : ℕ) : Prop :=
  ∀ p q : ℕ, Q0 ≤ q → 0 < q → 1 / (q:ℝ)^μ ≤ |Real.log 3 / Real.log 2 - (p:ℝ)/q|

/-- **Unconditional implication**: an irrationality measure `μ ≥ 1` from `Q0 ≥ 1` gives the integer
linear-form bound `2^L ≤ 2^2 k^{μ−1} (2^L − 3^k)` for `k ≥ Q0`, `3^k < 2^L`. -/
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

/-- **CONDITIONAL on `IrrMeasHyp μ Q0`**, `1 ≤ Q0 ≤ 225644606`, `μ ≥ 1`, `8(30+17(μ−1)+2) ≤ 2^16`:
every positive `T`-cycle point (any phase, any period) with `≤ 2` odd runs is `1` or `2`.
Steiner 1977 + Simons 2005 for all `k`, modulo the measure. -/
theorem few_runs_cycle_trivial_of_irrMeas {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ1 : 1 ≤ Q0)
    (hQ : Q0 ≤ 225644606) (hside : 8 * (30 + 17 * (μ-1) + 2) ≤ 2^16) (h : IrrMeasHyp μ Q0)
    {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) :
    x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm_tail_gap gapBelow_225644606 hside
    (linFormHyp_mono_K hQ (linFormHyp_mono_c (by norm_num) (linFormHyp_of_irrMeas hμ hQ1 h)))
    hx hL hc hr


/-- **C-level, CONDITIONAL on `IrrMeasHyp μ Q0`** (same side conditions): the canonical witness of
`state_of_the_art` for any nontrivial `C`-cycle has `≥ 3` odd runs. -/
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

/-- Named instance: `IrrMeasHyp 9 225644606` (Rhin-type `μ = 9`, threshold unverified) suffices. -/
theorem few_runs_cycle_trivial_of_irrMeas9 (H : IrrMeasHyp 9 225644606)
    {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) :
    x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_irrMeas (by norm_num) (by norm_num) le_rfl (by norm_num) H hx hL hc hr

/-- Sanity (unconditional): `IrrMeasHyp 1 1` is FALSE (`|log₂3 − 2| ≈ 0.415 < 1`). -/
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

/-- The side condition holds for `μ = 9`. -/
example : 8 * (30 + 17 * (9-1) + 2) ≤ 2^16 := by norm_num
example : 2^8 ≤ 2^2 * 5^(9-1) * (2^8 - 3^5) := by norm_num

end Collatz

#print axioms Collatz.linFormHyp_of_irrMeas
#print axioms Collatz.few_runs_cycle_trivial_of_irrMeas
#print axioms Collatz.state_of_the_art_of_irrMeas
#print axioms Collatz.few_runs_cycle_trivial_of_irrMeas9
#print axioms Collatz.not_irrMeasHyp_1_1
