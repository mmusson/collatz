/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import FareyBigChain
import RunsWindow

/-!
# A uniform gap for `2^L − 3^k` up to `k ≈ 3.15 · 10^50`

Let `p/q > log₂ 3 > p'/q'` be the consecutive convergents with
`q = 28501018847354252707686303092101337128713039628155` and
`q' = 286560769313560287561459075090682347932648071786258`, and let
`K1big = q + q' = 315061788160914540269145378182783685061361111414413`. The signs of `3^q − 2^p`
and `3^{q'} − 2^{p'}`, and the gap `1 − 3^q/2^p ≥ 2^{-170}`, follow from the certified brackets
of `FareyBigChain`; no power `3^q` is ever evaluated. By the Farey-neighbour lemma of `Farey`,
this gives `GapBelow K1big 170`.

We then extend the consequences of `Farey` to any `GapBelow K₁ s` with `s ≤ 20000`. In
particular, 1-circuits with `k < K1big` and 2-circuits with `k₁ + k₂ < K1big` are trivial, and a
positive `T`-cycle point with at most two odd runs and fewer than `K1big` odd steps is `1` or `2`.
With the run bounds of `RunsWindow`, the odd minimum of a cycle has at least `18` odd runs unless
`k ≥ K1big`, and at least `29` odd runs unless `k < 225644606` or `k ≥ K1big`.

## Main definitions

- `K1big`: the number `315061788160914540269145378182783685061361111414413`.

## Main results

- `gapBelow_K1big`: `GapBelow K1big 170`.
- `few_runs_cycle_trivial_of_lt_K1big`: a positive `T`-cycle point with at most two odd runs and
  fewer than `K1big` odd steps is `1` or `2`.
- `nontrivial_C_cycle_three_runs_K1big`: the corresponding statement for `C`-cycles.
- `runs_ge_18_K1big`, `runs_ge_29_K1big`: run bounds for the odd minimum of a `T`-cycle.
- `state_of_the_art_runs_K1big`, `state_of_the_art_runs_minimalPeriod_K1big`: these run bounds
  for nontrivial `C`-cycles, for any period and for the minimal period.

## References

- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
- R. P. Steiner, *A theorem on the Syracuse problem*, in Proc. 7th Manitoba Conference on
  Numerical Mathematics and Computing (1977), 553–559.
- J. L. Simons, *On the nonexistence of 2-cycles for the 3x+1 problem*, Math. Comp. 74 (2005),
  1565–1572.
- J. L. Simons, B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the
  3n+1 problem*, Acta Arith. 117 (2005), 51–70.
-/

namespace Collatz

open CollatzProof

/-! ### The gap at `K1big` -/

/-- A bracket for `R q (p + 1)` with lower end `> 1/2` gives `2^p < 3^q`. -/
theorem two_pow_lt_of_br_half {P A B q p : ℕ} (h : Br P A B q (p+1)) (hA : 2^P < 2*A) :
    2^p < 3^q := by
  have hA' : (2:ℚ)^P < 2*A := by exact_mod_cast hA
  have hD : (0:ℚ) < 2^P := by positivity
  have h1 : (1:ℚ)/2 < R q (p+1) := by
    refine lt_of_lt_of_le ?_ h.1
    rw [div_lt_div_iff₀ (by norm_num) hD]; linarith
  rw [R_def, pow_succ, div_lt_div_iff₀ (by norm_num) (by positivity)] at h1
  have : (2:ℚ)^p < 3^q := by nlinarith
  exact_mod_cast this

/-- The sum `q + q'` of the denominators of the two last certified convergents of `log₂ 3`. It is
an `abbrev` so that numeric tactics see the literal. -/
abbrev K1big : ℕ := 315061788160914540269145378182783685061361111414413

/-- `GapBelow K1big 170`: for `0 < k < K1big` and `3^k < 2^L`, `2^L ≤ 2^170 (2^L − 3^k)`. -/
theorem gapBelow_K1big : GapBelow K1big 170 := by
  have h := gapBelow_of_farey big_det (three_pow_lt_of_br big_above big_hB)
    (two_pow_lt_of_br big_below big_hA) (gap_of_br big_above big_hs)
  rw [big_K1] at h
  exact h

/-- `2^(p+p'−1) < 3^K1big`, from the bracket of the mediant. -/
theorem two_pow_lt_three_pow_K1big :
    2^499361119645202268103447277834341921011519769830461 < 3^K1big := by
  have h := big_med
  rw [big_M] at h
  exact two_pow_lt_of_br_half h big_hmed

/-! ### Consequences of a uniform gap `GapBelow K₁ s` -/

/-- `2^20000 · 3^50000 ≤ 4^50000` (checked by the kernel). -/
theorem cert_base_s : 2^20000 * 3^50000 ≤ 4^50000 := by decide +kernel

/-- `GapBelow K1 s` with `s ≤ 20000` gives the inequality of `TwoCircHyp` on `[10^5, K1)`. -/
theorem twoCirc_of_gap_s {K1 s k L : ℕ} (hG : GapBelow K1 s) (hs : s ≤ 20000)
    (hk : 100000 ≤ k) (hK : k < K1) (hL : 3^k < 2^L) :
    2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k) := by
  set h := k / 2 with hh
  have h50 : 50000 ≤ h := by omega
  have h2h : 2 * h ≤ k := Nat.mul_div_le k 2
  have s1 : 2^(h+1) + 3^h ≤ 2 * 3^h := by
    have := two_pow_succ_le_three_pow (h := h) (by omega); omega
  have s2 : 2^s * 3^h ≤ 4^h := by
    obtain ⟨t, ht⟩ : ∃ t, h = 50000 + t := ⟨h - 50000, by omega⟩
    rw [ht, pow_add, pow_add, ← mul_assoc]
    have : 2^s * 3^50000 ≤ 2^20000 * 3^50000 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hs)
    exact Nat.mul_le_mul (this.trans cert_base_s) (Nat.pow_le_pow_left (by norm_num) t)
  have s3 : 4^h ≤ 2^k := by
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) h2h
  have s4 : 2^s * (2^(h+1) + 3^h) ≤ 2^(k+1) := by
    calc 2^s * (2^(h+1) + 3^h) ≤ 2^s * (2 * 3^h) := Nat.mul_le_mul_left _ s1
      _ = 2 * (2^s * 3^h) := by ring
      _ ≤ 2 * 2^k := Nat.mul_le_mul_left _ (s2.trans s3)
      _ = 2^(k+1) := by ring
  have G := hG k L (by omega) hK hL
  set S := 2^(h+1) + 3^h
  set D := 2^L - 3^k
  have h30 : 0 < 2^s := by positivity
  apply Nat.le_of_mul_le_mul_left _ h30
  calc 2^s * (2^L * S) = 2^L * (2^s * S) := by ring
    _ ≤ 2^L * 2^(k+1) := Nat.mul_le_mul_left _ s4
    _ ≤ (2^s * D) * 2^(k+1) := Nat.mul_le_mul_right _ G
    _ = 2^s * (2^(k+1) * D) := by ring

/-- Under `GapBelow K1 s` with `s ≤ 20000`, every 1-circuit with `k < K1` has `m = 1`. -/
theorem one_circuit_eq_one_of_gap_s {K1 s m k l : ℕ} (hG : GapBelow K1 s) (hs : s ≤ 20000)
    (h : IsOneCircuit m k l) (hk : k < K1) : m = 1 := by
  rcases Nat.lt_or_ge k 100000 with hk' | hk'
  · exact one_circuit_eq_one h hk'
  · exact (one_circuit_false_of_at (fun _ hL => twoCirc_of_gap_s hG hs hk' hk hL) h).elim

/-- Under `GapBelow K1 s` with `s ≤ 20000`, every 2-circuit with `k1 + k2 < K1` has `m = 1`. -/
theorem two_circuit_eq_one_of_gap_s {K1 s m k1 l1 k2 l2 : ℕ} (hG : GapBelow K1 s)
    (hs : s ≤ 20000) (h : IsTwoCircuit m k1 l1 k2 l2) (hk : k1 + k2 < K1) : m = 1 := by
  rcases Nat.lt_or_ge (k1 + k2) 100000 with hk' | hk'
  · exact two_circuit_eq_one h hk'
  · exact (two_circuit_false_of_at (fun _ hL => twoCirc_of_gap_s hG hs hk' hk hL) h).elim

/-- Under `GapBelow K1 s` with `s ≤ 20000`, a positive `T`-cycle point with at most two odd runs
and fewer than `K1` odd steps is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_gap_s {K1 s x L : ℕ} (hG : GapBelow K1 s) (hs : s ≤ 20000)
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2)
    (hk : oddSteps L x < K1) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_core hx hL hc hr
    (fun m k l h e => one_circuit_eq_one_of_gap_s hG hs h
      (by rw [one_circuit_oddSteps h] at e; omega))
    (fun m k1 l1 k2 l2 h e =>
      two_circuit_eq_one_of_gap_s hG hs h (by rw [two_circuit_oddSteps h] at e; omega))

/-- Under `GapBelow K1 s` with `s ≤ 20000` and `2^M < 3^K1`, every nontrivial `C`-cycle gives an
odd `T`-cycle point `m ≥ 2^17` whose window either has at least three odd runs, or has at least
`K1` odd steps and length `L > M`. -/
theorem nontrivial_C_cycle_three_runs_of_gap_s {K1 s M : ℕ} (hG : GapBelow K1 s)
    (hs : s ≤ 20000) (hM : 2^M < 3^K1) (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) ∧
      ((K1 ≤ oddSteps L m ∧ M < L) ∨ 3 ≤ oddRuns L m) := by
  obtain ⟨m, L, a1, a2, a3, a4, a5, a6, a7⟩ := nontrivial_C_cycle_runs n hn ℓ hℓ h h1 h2 h4
  have : (2:ℕ)^17 = 131072 := by norm_num
  refine ⟨m, L, a1, a2, a3, a4, a5, a6, a7, ?_⟩
  rcases Nat.lt_or_ge (oddRuns L m) 3 with hr | hr
  · left
    rcases Nat.lt_or_ge (oddSteps L m) K1 with hk | hk
    · rcases few_runs_cycle_trivial_of_gap_s hG hs (by omega) a4 a5 (by omega) hk with e | e <;>
        omega
    · exact ⟨hk, lt_of_pow_certs hM hk (three_pow_lt_two_pow_of_cycle (by omega) a4 a5)⟩
  · exact Or.inr hr

/-! ### Circuits and cycles below `K1big` -/

/-- Every 1-circuit with `k < K1big` odd steps has `m = 1`. -/
theorem one_circuit_eq_one_of_lt_K1big {m k l : ℕ} (h : IsOneCircuit m k l) (hk : k < K1big) :
    m = 1 :=
  one_circuit_eq_one_of_gap_s gapBelow_K1big (by norm_num) h hk

/-- Every 2-circuit with `k1 + k2 < K1big` has `m = 1`. -/
theorem two_circuit_eq_one_of_lt_K1big {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2)
    (hk : k1 + k2 < K1big) : m = 1 :=
  two_circuit_eq_one_of_gap_s gapBelow_K1big (by norm_num) h hk

/-- A positive `T`-cycle point `x` (at any phase, for any period `L > 0`) whose window has at most
two odd runs and fewer than `K1big ≈ 3.15 · 10^50` odd steps is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_lt_K1big {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < K1big) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_gap_s gapBelow_K1big (by norm_num) hx hL hc hr hk

/-- A nontrivial positive `C`-cycle point `n` yields an odd `T`-cycle point `m` with
`2^17 ≤ m ≤ n` whose window either has at least three odd runs, or has at least `K1big` odd steps
and length `L > 499361119645202268103447277834341921011519769830461`. -/
theorem nontrivial_C_cycle_three_runs_K1big (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) ∧
      ((K1big ≤ oddSteps L m ∧ 499361119645202268103447277834341921011519769830461 < L) ∨
        3 ≤ oddRuns L m) :=
  nontrivial_C_cycle_three_runs_of_gap_s gapBelow_K1big (by norm_num) two_pow_lt_three_pow_K1big
    n hn ℓ hℓ h h1 h2 h4

/-! ### Run bounds below `K1big` -/

/-- `875 W r < 225644606 · 5^r` for `1 ≤ r ≤ 28`; this fails at `r = 29`. -/
theorem W_lt_225644606 (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ 28) : 875 * W r < 225644606 * 5^r := by
  interval_cases r <;> simp [W]

/-- Both run bounds at once; see `runs_ge_29_K1big` and `runs_ge_18_K1big`. -/
private theorem runs_bounds_K1big_aux {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) :
    (29 ≤ oddRuns L m ∨ oddSteps L m < 225644606 ∨ K1big ≤ oddSteps L m) ∧
    (18 ≤ oddRuns L m ∨ K1big ≤ oddSteps L m) := by
  have h24' : (16777216 : ℕ) ≤ m := by norm_num at h24; exact h24
  have hm0 : 0 < m := by omega
  have h3k := three_pow_lt_two_pow_of_cycle hm0 hL hc
  have hr1 := oddRuns_pos_of_cycle hm0 hL hc
  have hk0 := oddSteps_pos_of_cycle hm0 hL hc
  have hi : 29 ≤ oddRuns L m ∨ oddSteps L m < 225644606 ∨ K1big ≤ oddSteps L m := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hr, hkl, hkK⟩ := hcon
    have gap := gapBelow_K1big _ L hk0 hkK h3k
    have rb := runs_bound_of_min (s := 170) (t := 5) hodd hL hc hmin h3k gap
      (le_trans (by omega : oddRuns L m ≤ 32) (by norm_num))
    have hw := W_lt_225644606 _ hr1 (by omega)
    generalize oddRuns L m = r at rb hw
    generalize oddSteps L m = k at rb hkl
    have : 5^r * 225644606 ≤ 5^r * k := Nat.mul_le_mul_left _ hkl
    omega
  refine ⟨hi, ?_⟩
  have hA := runs_ge_18_of_min_window hodd h24 hmin hL hc
  rcases hi with h | h | h
  · left; omega
  · rcases hA with h' | h'
    · exact Or.inl h'
    · omega
  · exact Or.inr h

/-- For odd `m ≥ 2^24`, minimal on its `T`-orbit, and any `L > 0` with `T^[L] m = m`, the window
has at least `29` odd runs, or fewer than `225644606` odd steps, or at least `K1big` odd steps. -/
theorem runs_ge_29_K1big {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) :
    29 ≤ oddRuns L m ∨ oddSteps L m < 225644606 ∨ K1big ≤ oddSteps L m :=
  (runs_bounds_K1big_aux hodd h24 hmin hL hc).1

/-- For odd `m ≥ 2^24`, minimal on its `T`-orbit, and any `L > 0` with `T^[L] m = m`, the window
has at least `18` odd runs or at least `K1big` odd steps. -/
theorem runs_ge_18_K1big {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) :
    18 ≤ oddRuns L m ∨ K1big ≤ oddSteps L m :=
  (runs_bounds_K1big_aux hodd h24 hmin hL hc).2

/-- A positive `C`-cycle point `n ∉ {1, 2, 4}` yields the odd `T`-orbit minimum `m` with
`2^24 ≤ m ≤ n`, period `L > 0` and `k = oddSteps L m ≥ 12276` such that: there are at least `18`
odd runs or `k ≥ K1big`; there are at least `29` odd runs or `k < 225644606` or `k ≥ K1big`; and
there are at least `62` odd runs or `k ≥ 190537`. -/
theorem state_of_the_art_runs_K1big (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      12276 ≤ oddSteps L m ∧
      (18 ≤ oddRuns L m ∨ K1big ≤ oddSteps L m) ∧
      (29 ≤ oddRuns L m ∨ oddSteps L m < 225644606 ∨ K1big ≤ oddSteps L m) ∧
      (62 ≤ oddRuns L m ∨ 190537 ≤ oddSteps L m) := by
  obtain ⟨m, L, h1, h2, h3, h4, h5, h6, h7, -, h9⟩ := state_of_the_art_runs n hn ℓ hℓ h hne
  exact ⟨m, L, h1, h2, h3, h4, h5, h6, h7, runs_ge_18_K1big h1 h2 h6 h4 h5,
    runs_ge_29_K1big h1 h2 h6 h4 h5, h9⟩

/-- The bounds of `state_of_the_art_runs_K1big` for the minimal period
`Function.minimalPeriod T m`. -/
theorem state_of_the_art_runs_minimalPeriod_K1big (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < Function.minimalPeriod T m ∧ T^[Function.minimalPeriod T m] m = m ∧
      (18 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        K1big ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (29 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        oddSteps (Function.minimalPeriod T m) m < 225644606 ∨
        K1big ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (62 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        190537 ≤ oddSteps (Function.minimalPeriod T m) m) := by
  obtain ⟨m, h1, h2, h3, h6, hP, hPc, -, hB⟩ :=
    state_of_the_art_runs_minimalPeriod n hn ℓ hℓ h hne
  exact ⟨m, h1, h2, h3, h6, hP, hPc, runs_ge_18_K1big h1 h2 h6 hP hPc,
    runs_ge_29_K1big h1 h2 h6 hP hPc, hB⟩

/-! ### Examples -/

-- The trivial cycle satisfies the hypotheses of `few_runs_cycle_trivial_of_lt_K1big`.
example : 0 < 1 ∧ 0 < 2 ∧ T^[2] 1 = 1 ∧ oddRuns 2 1 ≤ 2 ∧ oddSteps 2 1 < K1big := by decide

end Collatz
