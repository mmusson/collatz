import CollatzSearch.FareyBig
import CollatzSearch.IrrMeasure

/-!
# Conditional interfaces now only need the tail `k ≥ K1big ≈ 3.15·10^50`

Generalizations of the `LinFormHyp`-tail lemmas of `Farey.lean` to `GapBelow K1 s`
(`s ≤ 20000`), and the `IrrMeasHyp` corollaries with threshold `Q0 ≤ K1big` instead of
`Q0 ≤ 225644606`.  **CONDITIONAL** on the unproved `IrrMeasHyp μ Q0` (a definition, not an
axiom; vacuous if false).  Rhin's exponent 8.616 is known only with a non-explicit threshold,
so even `Q0 ≤ 3.15·10^50` is not supplied by any located publication.  NOT Goal progress.
-/

namespace CollatzSearch
open CollatzProof

/-- CONDITIONAL (on `LinFormHyp K1 c μ`): with `GapBelow K1 s`, `s ≤ 20000`, and
`8(c+17μ+2) ≤ 2^16`, `TwoCircHyp 100000` holds. -/
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

/-- CONDITIONAL (on `LinFormHyp K1 c μ`): every positive `T`-cycle point with `≤ 2` odd runs
is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail_gap_s {K1 s c μ : ℕ} (hG : GapBelow K1 s)
    (hs : s ≤ 20000) (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 := by
  have H' := twoCircHyp_of_linForm_tail_gap_s hG hs h0 H
  exact few_runs_cycle_trivial_core hx hL hc hr
    (fun m k l h _ => one_circuit_eq_one_of_hyp H' h)
    (fun m k1 l1 k2 l2 h _ => two_circuit_eq_one_of_hyp H' h)

/-- **CONDITIONAL on `IrrMeasHyp μ Q0`**, now with `2 ≤ Q0 ≤ K1big ≈ 3.15·10^50`
(previously `Q0 ≤ 225644606`), `μ ≥ 1`, `8(30+17(μ−1)+2) ≤ 2^16`: every positive `T`-cycle
point (any phase, any period) with `≤ 2` odd runs is `1` or `2`. Requires `2 ≤ Q0` (for `Q0 ≤ 1`, `IrrMeasHyp` is false by
`IrrMeasureReal.not_irrMeasHyp_of_Q0_le_one`; strengthened from `1 ≤ Q0` in an earlier file). -/
theorem few_runs_cycle_trivial_of_irrMeas_big {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ2 : 2 ≤ Q0)
    (hQ : Q0 ≤ K1big) (hside : 8 * (30 + 17 * (μ-1) + 2) ≤ 2^16) (h : IrrMeasHyp μ Q0)
    {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) :
    x = 1 ∨ x = 2 := by
  have hQ1 : 1 ≤ Q0 := by omega
  exact few_runs_cycle_trivial_of_linForm_tail_gap_s gapBelow_big (by norm_num) hside
    (linFormHyp_mono_K hQ (linFormHyp_mono_c (by norm_num) (linFormHyp_of_irrMeas hμ hQ1 h)))
    hx hL hc hr

/-- **C-level, CONDITIONAL on `IrrMeasHyp μ Q0`**, `2 ≤ Q0 ≤ K1big`: the canonical witness of
`state_of_the_art` for any nontrivial `C`-cycle has `≥ 3` odd runs.  NOT Goal progress. Requires `2 ≤ Q0` (for `Q0 ≤ 1`, `IrrMeasHyp` is false by
`IrrMeasureReal.not_irrMeasHyp_of_Q0_le_one`; strengthened from `1 ≤ Q0` in an earlier file). -/
theorem state_of_the_art_of_irrMeas_big {μ Q0 : ℕ} (hμ : 1 ≤ μ) (hQ2 : 2 ≤ Q0)
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
  rcases few_runs_cycle_trivial_of_irrMeas_big hμ hQ2 hQ hside H (x := m) (by omega) h4 h5
    (by omega) with e | e <;> omega

end CollatzSearch

#print axioms CollatzSearch.twoCircHyp_of_linForm_tail_gap_s
#print axioms CollatzSearch.few_runs_cycle_trivial_of_linForm_tail_gap_s
#print axioms CollatzSearch.few_runs_cycle_trivial_of_irrMeas_big
#print axioms CollatzSearch.state_of_the_art_of_irrMeas_big
