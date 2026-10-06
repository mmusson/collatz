import MRuns
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Window-free (every period, hence per-lap) versions of the m-run bounds

**CLASSICAL** (Simons–de Weger 2005 m-cycle method, finite-range instance at verified range
`2^24`).  **NOT progress on `no_nontrivial_cycles`**.

`state_of_the_art_runs` (MRuns.lean) bounds `oddRuns L m` only for an existentially chosen
window `L`.  Here the bounds are proved for **every** `L > 0` with `T^[L] m = m`
(`runs_bounds_of_min_window`, `state_of_the_art_runs_all`), and in particular for
`L = Function.minimalPeriod T m`, i.e. per lap (`state_of_the_art_runs_minimalPeriod`).
The same is done for the result **CONDITIONAL** on the unformalized `LMNHyp`.
-/

namespace Collatz
open CollatzProof

/-- **Window-free core (unconditional).** For an odd `m ≥ 2^24` that is minimal on its `T`-orbit,
and **any** `L > 0` with `T^[L] m = m`:
(`oddRuns L m ≥ 18` or `oddSteps L m ≥ 225644606`) and
(`oddRuns L m ≥ 62` or `oddSteps L m ≥ 190537`). -/
theorem runs_bounds_of_min_window {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) :
    (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
    (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) := by
  have h24' : (16777216 : ℕ) ≤ m := by norm_num at h24; exact h24
  have hm0 : 0 < m := by omega
  have h3k := three_pow_lt_two_pow_of_cycle hm0 hL hc
  have hineq := cycle_run_ineq hm0 hc hmin
  have hr1 := oddRuns_pos_of_cycle hm0 hL hc
  have hk0 := oddSteps_pos_of_cycle hm0 hL hc
  have hsec : 62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m := by
    by_contra hcon
    push Not at hcon
    exact farey_runs_190537 hk0 hcon.2 h3k h24 (by omega) hineq
  refine ⟨?_, hsec⟩
  by_contra hcon
  push Not at hcon
  have hk2 : 190537 ≤ oddSteps L m := by omega
  have gap := gapBelow_225644606 _ L (by omega) hcon.2 h3k
  have rb := runs_bound_of_min (t := 5) hodd hL hc hmin h3k gap
    (le_trans (by omega : oddRuns L m ≤ 32) (by norm_num))
  have hw := W_small _ hr1 (by omega)
  generalize oddRuns L m = r at rb hw
  generalize oddSteps L m = k at rb hk2
  have : 5^r * 190537 ≤ 5^r * k := Nat.mul_le_mul_left _ hk2
  omega

/-- **Window-free core, CONDITIONAL on `LMNHyp`** (unformalized transcription of LMN 1995 /
Laurent 2008; vacuous if false): under the hypotheses of `runs_bounds_of_min_window`,
`oddRuns L m ≥ 14` for **every** period `L > 0`. -/
theorem runs_bounds_of_min_window_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2)
    (hc0 : c0 ≤ 1) (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0)
    {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) :
    14 ≤ oddRuns L m := by
  obtain ⟨hA, -⟩ := runs_bounds_of_min_window hodd h24 hmin hL hc
  by_contra hcon
  push Not at hcon
  have h24' : (16777216 : ℕ) ≤ m := by norm_num at h24; exact h24
  have hm0' : 0 < m := by omega
  have h3k := three_pow_lt_two_pow_of_cycle hm0' hL hc
  have hr1 := oddRuns_pos_of_cycle hm0' hL hc
  have hk : 225644606 ≤ oddSteps L m := by omega
  have gap := gap_of_LMN hC0 hC hc0 hm0 hm1 H (by omega) h3k
  have rb := runs_bound_of_min (t := 4) hodd hL hc hmin h3k gap
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

/-- **Unconditional, every window.** A positive `C`-cycle point `n ∉ {1,2,4}` yields an odd
`m`, `2^24 ≤ m ≤ n`, `T`-periodic and minimal on its `T`-orbit, such that for **every** `L > 0`
with `T^[L] m = m`: (`oddRuns L m ≥ 18` or `oddSteps L m ≥ 225644606`) and
(`oddRuns L m ≥ 62` or `oddSteps L m ≥ 190537`).  Classical. -/
theorem state_of_the_art_runs_all (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∃ L, 0 < L ∧ T^[L] m = m) ∧ (∀ j, m ≤ T^[j] m) ∧
      ∀ L, 0 < L → T^[L] m = m →
        (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
        (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) := by
  obtain ⟨m, L0, h1, h2, h3, h4, h5, h6, -⟩ := state_of_the_art_runs n hn ℓ hℓ h hne
  exact ⟨m, h1, h2, h3, ⟨L0, h4, h5⟩, h6,
    fun L hL hc => runs_bounds_of_min_window h1 h2 h6 hL hc⟩

/-- **Unconditional, per lap.** As `state_of_the_art_runs_all`, specialised to the minimal
period `P = Function.minimalPeriod T m > 0`: (`oddRuns P m ≥ 18` or `oddSteps P m ≥ 225644606`)
and (`oddRuns P m ≥ 62` or `oddSteps P m ≥ 190537`).  So no nontrivial cycle has, per lap,
`≤ 17` odd runs and `< 225,644,606` odd steps.  Classical. -/
theorem state_of_the_art_runs_minimalPeriod (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < Function.minimalPeriod T m ∧ T^[Function.minimalPeriod T m] m = m ∧
      (18 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        225644606 ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (62 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        190537 ≤ oddSteps (Function.minimalPeriod T m) m) := by
  obtain ⟨m, h1, h2, h3, ⟨L0, hL0, hc0⟩, h6, hall⟩ := state_of_the_art_runs_all n hn ℓ hℓ h hne
  have hP : 0 < Function.minimalPeriod T m :=
    Function.minimalPeriod_pos_of_mem_periodicPts (Function.mk_mem_periodicPts hL0 hc0)
  have hPc : T^[Function.minimalPeriod T m] m = m := Function.iterate_minimalPeriod
  exact ⟨m, h1, h2, h3, h6, hP, hPc, hall _ hP hPc⟩

/-- **CONDITIONAL on `LMNHyp`, every window.** The conclusion of `state_of_the_art_runs_all`
plus `oddRuns L m ≥ 14` for every period `L > 0`. -/
theorem state_of_the_art_runs_all_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2)
    (hc0 : c0 ≤ 1) (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∃ L, 0 < L ∧ T^[L] m = m) ∧ (∀ j, m ≤ T^[j] m) ∧
      ∀ L, 0 < L → T^[L] m = m →
        (18 ≤ oddRuns L m ∨ 225644606 ≤ oddSteps L m) ∧
        (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) ∧ 14 ≤ oddRuns L m := by
  obtain ⟨m, h1, h2, h3, hper, h6, hall⟩ := state_of_the_art_runs_all n hn ℓ hℓ h hne
  exact ⟨m, h1, h2, h3, hper, h6, fun L hL hc =>
    ⟨(hall L hL hc).1, (hall L hL hc).2,
      runs_bounds_of_min_window_LMN hC0 hC hc0 hm0 hm1 H h1 h2 h6 hL hc⟩⟩

/-- **CONDITIONAL on `LMNHyp`, per lap**: at `P = Function.minimalPeriod T m`,
`oddRuns P m ≥ 14` together with the unconditional per-lap disjunctions. -/
theorem state_of_the_art_runs_minimalPeriod_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst)
    (hC : Cst ≤ 51/2) (hc0 : c0 ≤ 1) (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < Function.minimalPeriod T m ∧ T^[Function.minimalPeriod T m] m = m ∧
      (18 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        225644606 ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (62 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        190537 ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      14 ≤ oddRuns (Function.minimalPeriod T m) m := by
  obtain ⟨m, h1, h2, h3, h6, hP, hPc, hA, hB⟩ :=
    state_of_the_art_runs_minimalPeriod n hn ℓ hℓ h hne
  exact ⟨m, h1, h2, h3, h6, hP, hPc, hA, hB,
    runs_bounds_of_min_window_LMN hC0 hC hc0 hm0 hm1 H h1 h2 h6 hP hPc⟩

/-- Per-lap instance, **CONDITIONAL** on `LMNHyp 25.2 0.21 20` (Laurent 2008, see `LMN.lean`). -/
theorem state_of_the_art_runs_minimalPeriod_of_Laurent08 (H : LMNHyp 25.2 0.21 20)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < Function.minimalPeriod T m ∧ T^[Function.minimalPeriod T m] m = m ∧
      (18 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        225644606 ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (62 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        190537 ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      14 ≤ oddRuns (Function.minimalPeriod T m) m :=
  state_of_the_art_runs_minimalPeriod_of_LMN (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) H n hn ℓ hℓ h hne

end Collatz

#print axioms Collatz.runs_bounds_of_min_window
#print axioms Collatz.runs_bounds_of_min_window_LMN
#print axioms Collatz.state_of_the_art_runs_all
#print axioms Collatz.state_of_the_art_runs_minimalPeriod
#print axioms Collatz.state_of_the_art_runs_all_of_LMN
#print axioms Collatz.state_of_the_art_runs_minimalPeriod_of_LMN
#print axioms Collatz.state_of_the_art_runs_minimalPeriod_of_Laurent08
