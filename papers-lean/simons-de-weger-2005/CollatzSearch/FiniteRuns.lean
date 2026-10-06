import CollatzSearch.RunsTail
import CollatzSearch.BackCong
import CollatzSearch.Milestones
import CollatzSearch.CycleBasic
import CollatzSearch.CycleWord
import Mathlib.Tactic

/-!
# Finitely many cycles with at most `R` odd runs per minimal `T`-lap (explicit)

**Status: Unconditional, CLASSICAL.** Finiteness of Collatz `m`-cycles for each fixed `m`
(cycles with at most `m` odd runs per lap) is classical: Steiner 1977 (`m = 1`) and
Simons–de Weger 2005 (Acta Arith. 117), both via Baker's theory of linear forms in logarithms.
What is new here is only the first formalization (kernel-checked) with an explicit bound; it uses
an elementary effective irrationality measure of `log₂ 3` (the in-house Padé measure
`linFormHyp_uncond`, `PadeSup`/`FewRunsUncond`/`RunsTail`), as is standard (cf. Rhin 1987), in place of Baker's theory.
**`FinitelyManyCycles` and `no_nontrivial_cycles` remain OPEN**: a general cycle may have
arbitrarily many odd runs; `R` is fixed here.

**Citations / label (`SyllableRotate`/`SyllableGrowth` repair).** First formalization of Brox / Luca / Simons–de Weger-strength
finiteness.  Related: Brox 2000 (Acta Arith. 92, 181–188: finitely many cycles with
`d(C) < 2 log|C|` descents); Luca 2005 (SUT J. Math. 41: a cycle has `≥ C₁ log n` ascents).

* `two_pow_mul_T_iter_le`: `2^j · T^j n ≤ 4^{S_j(n)} · n`.
* `L_le_two_oddSteps`: a positive `T`-cycle point has `L ≤ 2 S_L(m)`.
* `exp_tail`: `5(343+341e+R)·8^R < 3·2^e` for `e ≥ 4R+16`.
* `oddSteps_lt_of_runs`, `period_lt_of_runs`: an odd orbit minimum `m` of a `T`-cycle with
  `r = oddRuns L m` odd runs has `S_L(m) < 2^{4r+100}` and `L < 2^{4r+101}` (every `k`).
* `finite_T_cycles_bounded_runs`, `finite_cycleMinima_bounded_runs`: for each `R`, only
  finitely many cycles (as odd `T`-orbit minima / as elements of `CycleMinima`) have at most
  `R` odd runs per lap.
* `ncard_cycleMinima_bounded_runs_le`: their number is at most `2^{2^{4R+101}+1}` (crude).
* `finitelyManyCycles_iff_runs_bounded`: the milestone `FinitelyManyCycles` is EQUIVALENT to a
  uniform bound on the number of odd runs per lap over all cycles (a reformulation, not a proof).
-/

namespace CollatzSearch
open CollatzProof

/-- `2^j · T^j(n) ≤ 4^{S_j(n)} · n`: each even step halves, each odd step at most doubles
(`2·T n = 3n+1 ≤ 4n`). -/
theorem two_pow_mul_T_iter_le (j n : ℕ) : 2^j * T^[j] n ≤ 4^(oddSteps j n) * n := by
  induction j generalizing n with
  | zero => simp [oddSteps]
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    simp only [oddSteps]
    have key : 2 * T n ≤ 4^(n%2) * n := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [h, pow_zero, T_of_even h]; omega
      · rw [h, pow_one, T_of_odd h]; omega
    calc 2^(j+1) * T^[j] (T n) = 2 * (2^j * T^[j] (T n)) := by ring
      _ ≤ 2 * (4^(oddSteps j (T n)) * T n) := Nat.mul_le_mul_left _ (ih _)
      _ = 4^(oddSteps j (T n)) * (2 * T n) := by ring
      _ ≤ 4^(oddSteps j (T n)) * (4^(n%2) * n) := Nat.mul_le_mul_left _ key
      _ = 4^(oddSteps j (T n) + n%2) * n := by rw [pow_add]; ring

/-- A positive point of a `T`-cycle of length `L` satisfies `L ≤ 2·S_L(m)`: at least half of
the steps of the lap are odd. -/
theorem L_le_two_oddSteps {m L : ℕ} (hm : 0 < m) (hc : T^[L] m = m) : L ≤ 2 * oddSteps L m := by
  have h := two_pow_mul_T_iter_le L m
  rw [hc, show (4:ℕ) = 2^2 by norm_num, ← pow_mul] at h
  have h2 := Nat.le_of_mul_le_mul_right h hm
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

/-- Exponential tail inequality: `5(343+341e+R)·8^R < 3·2^e` whenever `e ≥ 4R+16`. -/
theorem exp_tail (R e : ℕ) (he : 4*R+16 ≤ e) : 5 * (343 + 341*e + R) * 8^R < 3 * 2^e := by
  induction e, he using Nat.le_induction with
  | base =>
    have hR : R < 2^R := Nat.lt_two_pow_self
    have h16 : 0 < 16^R := by positivity
    calc 5 * (343 + 341*(4*R+16) + R) * 8^R ≤ 28995 * (R+1) * 8^R :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ 28995 * 2^R * 8^R := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hR)
      _ = 28995 * 16^R := by rw [mul_assoc, ← mul_pow]; norm_num
      _ < 196608 * 16^R := by omega
      _ = 3 * 2^(4*R+16) := by rw [pow_add, pow_mul]; norm_num; ring
  | succ e he ih =>
    have h1 : 5 * 341 * 8^R ≤ 5 * (343 + 341*e + R) * 8^R :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have e1 : 5 * (343 + 341*(e+1) + R) * 8^R = 5 * (343 + 341*e + R) * 8^R + 5 * 341 * 8^R := by
      ring
    rw [e1, pow_succ 2 e, ← mul_assoc]
    exact tail_step h1 ih

/-- **Unconditional, CLASSICAL in substance (first formalization; uses an elementary effective
irrationality measure of `log₂ 3`, as is standard, cf. Rhin 1987).** If `m` is odd and minimal on
its `T`-orbit, `L > 0` and `T^L m = m`, then the number of odd steps satisfies
`S_L(m) < 2^{4·oddRuns L m + 100}`. Valid for every `k` (no range restriction). Proof:
`runs_bound_of_min` with gap exponent `2+341(⌊log₂k⌋+1)` from `linFormHyp_uncond` and `t = r`,
then `exp_tail`. -/
theorem oddSteps_lt_of_runs {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) : oddSteps L m < 2^(4 * oddRuns L m + 100) := by
  by_contra hK
  push Not at hK
  have hm0 : 0 < m := by omega
  have h3 := three_pow_lt_two_pow_of_cycle hm0 hL hc
  have ht : oddRuns L m ≤ 2^(oddRuns L m) := Nat.lt_two_pow_self.le
  set r := oddRuns L m with hrdef
  set k := oddSteps L m with hkdef
  have hk100 : 2^100 ≤ k := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hK
  have hk0 : k ≠ 0 := by positivity
  set e := Nat.log 2 k with hedef
  have hle : 2^e ≤ k := Nat.pow_log_le_self 2 hk0
  have hlt : k < 2^(e+1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have he : 4*r+100 ≤ e := by
    by_contra hcon
    push Not at hcon
    have : 2^(e+1) ≤ 2^(4*r+100) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlin := linFormHyp_uncond k L hk100 h3
  have hkp : k^341 ≤ 2^(341*(e+1)) := by
    rw [show 341*(e+1) = (e+1)*341 from Nat.mul_comm _ _, pow_mul]
    exact Nat.pow_le_pow_left hlt.le _
  have hgap : 2^L ≤ 2^(2 + 341*(e+1)) * (2^L - 3^k) := by
    calc 2^L ≤ 2^2 * k^341 * (2^L - 3^k) := hlin
      _ ≤ 2^2 * 2^(341*(e+1)) * (2^L - 3^k) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkp)
      _ = 2^(2 + 341*(e+1)) * (2^L - 3^k) := by rw [pow_add]
  have rb := runs_bound_of_min (s := 2 + 341*(e+1)) (t := r) hodd hL hc hmin h3 hgap ht
  rw [← hrdef, ← hkdef] at rb
  have hW := three_W_add r
  have tail := exp_tail r e (by omega)
  have hs : 2 + 341*(e+1) + r = 343 + 341*e + r := by ring
  rw [hs] at rb
  set A := 5 * (343 + 341*e + r) with hA
  have hApos : 0 < A := by rw [hA]; omega
  have h5 : 1 ≤ 5^r := Nat.one_le_pow _ _ (by norm_num)
  have s1 : 3 * (5^r * k) < A * 8^r := by
    calc 3 * (5^r * k) ≤ 3 * (A * W r) := Nat.mul_le_mul_left _ rb
      _ = A * (3 * W r) := by ring
      _ < A * 8^r := Nat.mul_lt_mul_of_pos_left (by omega) hApos
  have s2 : 3 * k ≤ 3 * (5^r * k) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ h5)
  omega

/-- Same hypotheses: the period satisfies `L < 2^{4·oddRuns L m + 101}`. -/
theorem period_lt_of_runs {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) : L < 2^(4 * oddRuns L m + 101) := by
  have h1 := L_le_two_oddSteps (by omega : 0 < m) hc
  have h2 := oddSteps_lt_of_runs hodd hmin hL hc
  rw [pow_succ]; omega

/-- Monotone form: `oddRuns L m ≤ R` gives `S_L(m) < 2^{4R+100}` and `L < 2^{4R+101}`. -/
theorem oddSteps_period_lt_of_runs_le {m L R : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m)
    (hL : 0 < L) (hc : T^[L] m = m) (hR : oddRuns L m ≤ R) :
    oddSteps L m < 2^(4 * R + 100) ∧ L < 2^(4 * R + 101) :=
  ⟨lt_of_lt_of_le (oddSteps_lt_of_runs hodd hmin hL hc)
      (Nat.pow_le_pow_right (by norm_num) (by omega)),
   lt_of_lt_of_le (period_lt_of_runs hodd hmin hL hc)
      (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-- Points of period at most `N`: `{x | ∃ L, 1 ≤ L ≤ N, T^L x = x}`. -/
def perUpTo (N : ℕ) : Set ℕ := {x | ∃ L, 1 ≤ L ∧ L ≤ N ∧ T^[L] x = x}

/-- Points of `T`-period at most `N` form a finite set of size `≤ 2^{N+1}` (union bound over
`periodic_ncard_le`). -/
theorem perUpTo_finite_ncard (N : ℕ) : (perUpTo N).Finite ∧ (perUpTo N).ncard ≤ 2^(N+1) := by
  induction N with
  | zero =>
    have : perUpTo 0 = ∅ := by
      ext x; simp only [perUpTo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨L, h1, h2, -⟩; omega
    rw [this]; simp
  | succ N ih =>
    have heq : perUpTo (N+1) = perUpTo N ∪ {x | T^[N+1] x = x} := by
      ext x; simp only [perUpTo, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨L, h1, h2, h3⟩
        rcases Nat.lt_or_ge L (N+1) with h | h
        · exact Or.inl ⟨L, h1, by omega, h3⟩
        · right; have : L = N+1 := by omega
          subst this; exact h3
      · rintro (⟨L, h1, h2, h3⟩ | h)
        · exact ⟨L, h1, by omega, h3⟩
        · exact ⟨N+1, by omega, le_rfl, h⟩
    obtain ⟨hf, hc⟩ := periodic_ncard_le (Nat.succ_pos N)
    rw [heq]
    refine ⟨ih.1.union hf, ?_⟩
    calc (perUpTo N ∪ {x | T^[N+1] x = x}).ncard
        ≤ (perUpTo N).ncard + {x | T^[N+1] x = x}.ncard := Set.ncard_union_le _ _
      _ ≤ 2^(N+1) + 2^(N+1) := Nat.add_le_add ih.2 hc
      _ = 2^(N+1+1) := by ring

/-- Odd orbit minima of `T`-cycles with at most `R` odd runs have period `≤ 2^{4R+101}`. -/
theorem T_cycles_bounded_runs_subset (R : ℕ) :
    {m : ℕ | m % 2 = 1 ∧ (∀ j, m ≤ T^[j] m) ∧ ∃ L, 0 < L ∧ T^[L] m = m ∧ oddRuns L m ≤ R}
      ⊆ perUpTo (2^(4*R+101)) := by
  rintro m ⟨hodd, hmin, L, hL, hc, hR⟩
  exact ⟨L, hL, (oddSteps_period_lt_of_runs_le hodd hmin hL hc hR).2.le, hc⟩

/-- **Unconditional, CLASSICAL (Steiner / Simons–de Weger; first formalization, explicit;
uses an elementary effective irrationality measure of `log₂ 3`, as is standard, cf. Rhin 1987).** For each `R`, the set of odd `m`, minimal on their `T`-orbit, lying on a `T`-cycle
with at most `R` odd runs per lap, is finite. -/
theorem finite_T_cycles_bounded_runs (R : ℕ) :
    {m : ℕ | m % 2 = 1 ∧ (∀ j, m ≤ T^[j] m) ∧ ∃ L, 0 < L ∧ T^[L] m = m ∧ oddRuns L m ≤ R}.Finite :=
  (perUpTo_finite_ncard _).1.subset (T_cycles_bounded_runs_subset R)

/-- A cycle minimum (for `C`) is odd, minimal on its `T`-orbit, and `T`-periodic. -/
theorem cycleMinima_T_props {n : ℕ} (hmem : n ∈ CycleMinima) :
    n % 2 = 1 ∧ (∀ j, n ≤ T^[j] n) ∧ ∃ L, 0 < L ∧ T^[L] n = n := by
  obtain ⟨⟨hn, ℓ, hℓ, h⟩, hminC⟩ := hmem
  obtain ⟨m, L, -, hmodd, hL, hLm, hminm, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux n hn ℓ hℓ h
  obtain ⟨ℓ', hℓ', hC⟩ := C_cycle_of_T_cycle hL hLm
  have per : C^[ℓ' * t] m = m := (Function.IsPeriodicPt.mul_const hC t).eq
  have hle : t ≤ ℓ' * t := Nat.le_mul_of_pos_left t hℓ'
  have hback : C^[ℓ' * t - t] n = m := by
    rw [← ht, ← Function.iterate_add_apply, Nat.sub_add_cancel hle, per]
  have hnm : n ≤ m := by have := hminC (ℓ' * t - t); rwa [hback] at this
  have : m = n := le_antisymm hmn hnm
  subst this
  exact ⟨hmodd, hminm, L, hL, hLm⟩

/-- Cycle minima with at most `R` odd runs per (minimal) `T`-lap lie in the `T`-level set. -/
theorem cycleMinima_bounded_runs_subset (R : ℕ) :
    {n : ℕ | n ∈ CycleMinima ∧ oddRuns (Function.minimalPeriod T n) n ≤ R} ⊆
      {m : ℕ | m % 2 = 1 ∧ (∀ j, m ≤ T^[j] m) ∧ ∃ L, 0 < L ∧ T^[L] m = m ∧ oddRuns L m ≤ R} := by
  rintro n ⟨hmem, hR⟩
  obtain ⟨hodd, hmin, L, hL, hc⟩ := cycleMinima_T_props hmem
  have hper : n ∈ Function.periodicPts T := ⟨L, hL, hc⟩
  exact ⟨hodd, hmin, _, Function.minimalPeriod_pos_of_mem_periodicPts hper,
    Function.iterate_minimalPeriod, hR⟩

/-- **Milestone weakening of `FinitelyManyCycles` (CLASSICAL; first formalization,
using an elementary effective irrationality measure of `log₂ 3`, as is standard, cf. Rhin
1987).** For every `R`, only finitely many Collatz cycles have at most `R` odd runs per minimal
`T`-lap:
`{n ∈ CycleMinima | oddRuns (minimalPeriod T n) n ≤ R}` is finite. `FinitelyManyCycles`
itself remains OPEN. -/
theorem finite_cycleMinima_bounded_runs (R : ℕ) :
    {n : ℕ | n ∈ CycleMinima ∧ oddRuns (Function.minimalPeriod T n) n ≤ R}.Finite :=
  (finite_T_cycles_bounded_runs R).subset (cycleMinima_bounded_runs_subset R)

/-- Explicit (crude) count: at most `2^{2^{4R+101}+1}` cycles have `≤ R` odd runs per lap. -/
theorem ncard_cycleMinima_bounded_runs_le (R : ℕ) :
    {n : ℕ | n ∈ CycleMinima ∧ oddRuns (Function.minimalPeriod T n) n ≤ R}.ncard ≤
      2^(2^(4*R+101)+1) :=
  le_trans (Set.ncard_le_ncard ((cycleMinima_bounded_runs_subset R).trans
      (T_cycles_bounded_runs_subset R)) (perUpTo_finite_ncard _).1)
    (perUpTo_finite_ncard _).2

/-- **Reformulation (not a proof) of the milestone.** `FinitelyManyCycles` holds iff there is a
uniform bound `R` on the number of odd runs per minimal `T`-lap of every cycle. The `←`
direction is `finite_cycleMinima_bounded_runs`; `→` takes the maximum over a finite set. -/
theorem finitelyManyCycles_iff_runs_bounded :
    FinitelyManyCycles ↔
      ∃ R, ∀ n ∈ CycleMinima, oddRuns (Function.minimalPeriod T n) n ≤ R := by
  constructor
  · intro hf
    obtain ⟨R, hR⟩ := (hf.image (fun n => oddRuns (Function.minimalPeriod T n) n)).bddAbove
    exact ⟨R, fun n hn => hR ⟨n, hn, rfl⟩⟩
  · rintro ⟨R, hR⟩
    exact (finite_cycleMinima_bounded_runs R).subset (fun n hn => ⟨hn, hR n hn⟩)

/-- Sanity (non-vacuity): the trivial cycle `1 → 2 → 1` has one odd run and lies in the set. -/
example : 1 ∈ {n : ℕ | n ∈ CycleMinima ∧ oddRuns (Function.minimalPeriod T n) n ≤ 1} := by
  refine ⟨one_mem_cycleMinima, ?_⟩
  have hp : Function.minimalPeriod T 1 = 2 := by
    have h2 : Function.IsPeriodicPt T 2 1 := by decide
    have hdvd := h2.minimalPeriod_dvd
    have hpos := h2.minimalPeriod_pos (by norm_num)
    have hne1 : Function.minimalPeriod T 1 ≠ 1 := by
      intro h1
      have := Function.iterate_minimalPeriod (f := T) (x := 1)
      rw [h1] at this; revert this; decide
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases (Function.minimalPeriod T 1) <;> simp_all
  rw [hp]; decide

end CollatzSearch
#print axioms CollatzSearch.oddSteps_lt_of_runs
#print axioms CollatzSearch.period_lt_of_runs
#print axioms CollatzSearch.finite_T_cycles_bounded_runs
#print axioms CollatzSearch.finite_cycleMinima_bounded_runs
#print axioms CollatzSearch.ncard_cycleMinima_bounded_runs_le
#print axioms CollatzSearch.finitelyManyCycles_iff_runs_bounded
#print axioms CollatzSearch.oddSteps_period_lt_of_runs_le
