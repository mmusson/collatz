import Farey24
import FareyStretch
import SchemeBridge

/-!
# State of the art (entry point since `Final`: `Collatz/Final.lean`)

One consolidated statement of what this library proves about a hypothetical nontrivial
positive Collatz cycle, all on the **same** cycle point: the odd minimum `m` of the orbit,
with period `L` of the accelerated map `T`, `k = S_L(m) = oddSteps L m`.

* `state_of_the_art` (**unconditional, classical**): `m` odd, `2^24 ≤ m ≤ n`, `m` minimal on
  its `T`-orbit, `k = 665a + 11611b`, `L = 1054a + 18403b` with `a, b ≥ 1` (so `k ≥ 12276`,
  `L ≥ 19457`), and the window has `≥ 3` odd runs unless `k ≥ 225644606`.
  Sources: Eliahou (1993) Farey decomposition, an Oliveira e Silva-type residue sieve for the
  verified range `2^24`, and finite-range instances of Steiner (1977) / Simons (2005)
  (1- and 2-circuit exclusion for `k < 225644606`).
* `state_of_the_art_of_scheme`, `state_of_the_art_of_linForm` (**CONDITIONAL** on the
  hypotheses `SchemeHyp a b c0` (+ numeric side condition), resp.
  `LinFormHyp 225644606 100 14`): the same `m` has `≥ 3` odd runs for every `k`.
  These are hypotheses believed to follow from published results (Rhin 1987 / Wu–Wang 2014 /
  LMN 1995) [`IrrMeasureReal`: Wu–Wang 2014, J. Number Theory, DOI 10.1016/j.jnt.2014.03.007, 'On the irrationality measure of log 3', concerns log 3, NOT log 3/log 2]; the implication with these exact constants has NOT been checked; wall (b)
  abandoned: sources unavailable; decoupled-Padé route heuristically obstructed (not proved).
  Note: the polynomial `LinFormHyp` is NOT implied by Baker/LMN-type bounds for large
  `k` (those are quasi-polynomial); superseded by `state_of_the_art_of_LMN` (`LMN.lean`).

The literature is far stronger (verified range `2^68`, Hercher 2023 excludes m-cycles for m ≤ 91).

**`FareyBigCore`/`FareyBigCond` note (appended).** The unconditional threshold `225644606` used here (for `≤ 2` odd
runs, and for the `≥ 18`-run ladder in `MRuns`/`RunsWindow`) is superseded by
`K1big = 315061788160914540269145378182783685061361111414413 ≈ 3.15·10^50` in
`FareyBig.lean` (`gapBelow_big`, `few_runs_cycle_trivial_big`,
`nontrivial_C_cycle_three_runs_big`, `runs_bounds_big`, `state_of_the_art_runs_big`,
`state_of_the_art_runs_minimalPeriod_big`), via certified interval arithmetic on `3^q/2^p`
(`FareyBigCore.lean`, generated chain `FareyBigChain.lean`).  For the conditional interfaces,
`FareyBigCond.lean` proves `few_runs_cycle_trivial_of_irrMeas_big` /
`state_of_the_art_of_irrMeas_big`: `IrrMeasHyp μ Q0` is needed only with `2 ≤ Q0 ≤ K1big`, i.e.
only for `k ≥ K1big`.  (The `ExpGap`/`LMN` interfaces have NOT been re-instantiated; for them
this is a remark only.)  Still classical;

**`RunsLog` note (appended).** `RunsLog.lean` (`runs_log_bound`, `runs_ge_42` … `runs_ge_233`,
`state_of_the_art_runs_log`): for the odd orbit-minimum of a cycle with `k = S_L(m) < K1big`,
the run lower bound now grows like `log_{8/5}(3k/890)` (`r ≥ 256` or `3·5^r·k < 890·8^r`;
e.g. `r ≥ 42` for `k ≥ 10^11`, `r ≥ 233` for `k ≥ 10^50`).  The fixed `≥ 29` rung of
`runs_bounds_big` is recovered, without `2^24 ≤ m`, as the theorem `runs_ge_29_of_log`
(`RunsLog.lean`, `Summary`).  Classical (a Simons–de Weger-type finite-range instance);
-/

namespace Collatz
open CollatzProof Collatz.Transfer

/-- **Unconditional state of the art.** A positive `C`-cycle point `n ∉ {1,2,4}` (period
`ℓ > 0`) yields an odd `T`-cycle point `m`, the minimum of its orbit, `2^24 ≤ m ≤ n`, with a
period `L > 0` such that `S_L(m) = 665a+11611b`, `L = 1054a+18403b` (`a,b ≥ 1`),
`S_L(m) ≥ 12276`, `L ≥ 19457`, and (`≥ 3` odd runs or `S_L(m) ≥ 225644606`). -/
theorem state_of_the_art (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L a b, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < a ∧ 0 < b ∧ oddSteps L m = 665*a + 11611*b ∧ L = 1054*a + 18403*b ∧
      12276 ≤ oddSteps L m ∧ 19457 ≤ L ∧
      (3 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) := by
  obtain ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL⟩ :=
    nontrivial_C_cycle_farey24 n hn ℓ hℓ h hne
  refine ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL, by omega, by omega, ?_⟩
  have h24 : (16777216 : ℕ) ≤ m := by norm_num at h2; exact h2
  by_contra hcon
  push Not at hcon
  rcases few_runs_cycle_trivial_farey2 (x := m) (by omega) h4 h5 (by omega) hcon.2 with e | e <;>
    omega

/-- **CONDITIONAL on the unproved `SchemeHyp a0 b0 c0`** (and the numeric side condition of
`few_runs_cycle_trivial_of_scheme`): the same conclusion as `state_of_the_art`, with the final
disjunction strengthened to `≥ 3` odd runs.

`SchemeHyp` is a hypothesis believed to follow from published results (Rhin 1987:
`μ ≤ 7.616`; Wu–Wang 2014: `μ ≈ 5.125`); implication not checked; vacuous if false.
`IrrMeasureReal` corrections: Rhin's 7.616 is the linear-form exponent, 8.616 the irrationality measure
(Wu 2003, Math. Comp. 72, p. 902); [`IrrMeasureReal`: Wu–Wang 2014, J. Number Theory, DOI 10.1016/j.jnt.2014.03.007, 'On the irrationality measure of log 3', concerns log 3, NOT log 3/log 2]. -/
theorem state_of_the_art_of_scheme {a0 b0 c0 : ℕ} (hS : SchemeHyp a0 b0 c0)
    (h0 : 8 * ((3 + 2*c0 + 2*a0*(2*c0+5)) + 17*(2*a0) + 2) ≤ 2^16)
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
  rcases few_runs_cycle_trivial_of_scheme hS h0 (x := m) (by omega) h4 h5 (by omega) with e | e <;>
    omega

/-- **CONDITIONAL on the unproved `LinFormHyp 225644606 100 14`** (SUPERSEDED in `LMN` by
`state_of_the_art_of_LMN`; `LinFormHyp` is not implied by LMN-type bounds for large `k`): the same conclusion as
`state_of_the_art`, with the final disjunction strengthened to `≥ 3` odd runs.

`LinFormHyp` is a hypothesis believed to follow from published results (Rhin 1987:
`μ ≤ 7.616`; Wu–Wang 2014: `μ ≈ 5.125`); implication not checked; vacuous if false.
`IrrMeasureReal` corrections: Rhin's 7.616 is the linear-form exponent, 8.616 the irrationality measure
(Wu 2003, Math. Comp. 72, p. 902); [`IrrMeasureReal`: Wu–Wang 2014, J. Number Theory, DOI 10.1016/j.jnt.2014.03.007, 'On the irrationality measure of log 3', concerns log 3, NOT log 3/log 2]. -/
theorem state_of_the_art_of_linForm (H : LinFormHyp 225644606 100 14)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L a b, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < a ∧ 0 < b ∧ oddSteps L m = 665*a + 11611*b ∧ L = 1054*a + 18403*b ∧
      12276 ≤ oddSteps L m ∧ 19457 ≤ L ∧ 3 ≤ oddRuns L m := by
  obtain ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL, hk', hL', -⟩ :=
    state_of_the_art n hn ℓ hℓ h hne
  refine ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL, hk', hL', ?_⟩
  have h24 : (16777216 : ℕ) ≤ m := by norm_num at h2; exact h2
  have H' : LinFormHyp 100000 100 14 := linFormHyp_of_tail2 (by norm_num) H
  by_contra hcon
  rcases few_runs_cycle_trivial_of_linForm le_rfl (by norm_num) H' (x := m) (by omega) h4 h5
    (by omega) with e | e <;> omega

end Collatz

#print axioms Collatz.state_of_the_art
#print axioms Collatz.state_of_the_art_of_scheme
#print axioms Collatz.state_of_the_art_of_linForm
