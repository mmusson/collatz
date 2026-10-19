/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import FareyBig
import IrrMeasure

/-!
# Irrationality-measure hypotheses needed only beyond `K1big`

This file generalizes the results of `Farey` that restrict `LinFormHyp` to large `k` from
`GapBelow K₁ 30` to `GapBelow K₁ s` with `s ≤ 20000`. Combined with `gapBelow_K1big`, it shows
that an irrationality-measure hypothesis `IrrMeasHyp μ Q₀` is needed only with threshold
`Q₀ ≤ K1big ≈ 3.15 · 10^50`, rather than `Q₀ ≤ 225644606`.

Results in this file assume the hypothesis `LinFormHyp` or `IrrMeasHyp μ Q₀`, which is not proved
here. Rhin's exponent `8.616` is known only with a non-explicit threshold, so even the threshold
`Q₀ ≤ K1big` is not supplied by the literature.

## Main results

- `twoCircHyp_of_linForm_tail_gap_s`: under `GapBelow K₁ s` with `s ≤ 20000`, the hypothesis
  `LinFormHyp K₁ c μ` with `8(c + 17μ + 2) ≤ 2^16` implies `TwoCircHyp 100000`.
- `few_runs_cycle_trivial_of_irrMeas_K1big`: under `IrrMeasHyp μ Q₀` with `2 ≤ Q₀ ≤ K1big`, every
  positive `T`-cycle point with at most two odd runs is `1` or `2`.
- `state_of_the_art_of_irrMeas_K1big`: under the same hypothesis, the cycle point of
  `state_of_the_art` has at least three odd runs.

## References

- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, in Séminaire de Théorie
  des Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
-/

namespace Collatz

open CollatzProof

/-! ### `LinFormHyp` beyond a uniform gap -/

/-- Under `GapBelow K1 s` with `s ≤ 20000`, `8(c + 17μ + 2) ≤ 2^16` and `LinFormHyp K1 c μ`,
`TwoCircHyp 100000` holds. -/
theorem twoCircHyp_of_linForm_tail_gap_s {K1 s c μ : ℕ} (hG : GapBelow K1 s) (hs : s ≤ 20000)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) : TwoCircHyp 100000 := by
  intro k L hk h3
  rcases Nat.lt_or_ge k K1 with hK | hK
  · exact twoCirc_of_gap_s hG hs hk hK h3
  · have hL := H k L hK h3
    have hg := growth (log_cond h0 k (by norm_num; omega))
    set S := 2^(k/2+1) + 3^(k/2)
    set D := 2^L - 3^k
    calc 2^L * S ≤ (2^c * k^μ * D) * S := Nat.mul_le_mul_right _ hL
      _ = (2^c * k^μ * S) * D := by ring
      _ ≤ 2^(k+1) * D := Nat.mul_le_mul_right _ hg.le

/-- Under the hypotheses of `twoCircHyp_of_linForm_tail_gap_s`, every positive `T`-cycle point
with at most two odd runs is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail_gap_s {K1 s c μ : ℕ} (hG : GapBelow K1 s)
    (hs : s ≤ 20000) (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 := by
  have H' := twoCircHyp_of_linForm_tail_gap_s hG hs h0 H
  exact few_runs_cycle_trivial_core hx hL hc hr
    (fun m k l h _ => one_circuit_eq_one_of_hyp H' h)
    (fun m k1 l1 k2 l2 h _ => two_circuit_eq_one_of_hyp H' h)

/-! ### Irrationality-measure hypotheses -/

/-- Under `IrrMeasHyp μ Q0` with `2 ≤ Q0 ≤ K1big`, `μ ≥ 1` and `8(30 + 17(μ − 1) + 2) ≤ 2^16`,
every positive `T`-cycle point (at any phase, for any period) with at most two odd runs is `1` or
`2`. The condition `2 ≤ Q0` costs nothing, since `IrrMeasHyp μ Q0` is false for `Q0 ≤ 1`. -/
theorem few_runs_cycle_trivial_of_irrMeas_K1big {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ2 : 2 ≤ Q0)
    (hQ : Q0 ≤ K1big) (hside : 8 * (30 + 17 * (μ-1) + 2) ≤ 2^16) (h : IrrMeasHyp μ Q0)
    {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) :
    x = 1 ∨ x = 2 := by
  have hQ1 : 1 ≤ Q0 := by omega
  exact few_runs_cycle_trivial_of_linForm_tail_gap_s gapBelow_K1big (by norm_num) hside
    (linFormHyp_mono_K hQ (linFormHyp_mono_c (by norm_num) (linFormHyp_of_irrMeas hμ hQ1 h)))
    hx hL hc hr

/-- Under the hypotheses of `few_runs_cycle_trivial_of_irrMeas_K1big`, the cycle point given by
`state_of_the_art` for a nontrivial `C`-cycle has at least three odd runs. -/
theorem state_of_the_art_of_irrMeas_K1big {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ2 : 2 ≤ Q0)
    (hQ : Q0 ≤ K1big) (hside : 8 * (30 + 17 * (μ-1) + 2) ≤ 2^16) (H : IrrMeasHyp μ Q0)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L a b, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < a ∧ 0 < b ∧ oddSteps L m = 665*a + 11611*b ∧ L = 1054*a + 18403*b ∧
      12276 ≤ oddSteps L m ∧ 19457 ≤ L ∧ 3 ≤ oddRuns L m := by
  have hQ1 : 1 ≤ Q0 := by omega
  obtain ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL, hk', hL', -⟩ :=
    state_of_the_art n hn ℓ hℓ h hne
  refine ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL, hk', hL', ?_⟩
  have h24 : (16777216 : ℕ) ≤ m := by norm_num at h2; exact h2
  by_contra hcon
  rcases few_runs_cycle_trivial_of_irrMeas_K1big hμ hQ2 hQ hside H (x := m) (by omega) h4 h5
    (by omega) with e | e <;> omega

end Collatz
