/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import FewRunsUncond
import RunsLog
import IrrMeasure
import Collatz.StateOfArt

/-!
# Run bounds for cycles with many odd steps

The run bounds of `RunsLog` and `FareyBig` hold for cycles with fewer than `K1big` odd steps. In
this file we treat the remaining range `k ≥ K1big` with an effective irrationality measure of
`log₂ 3`, obtained from the Padé witness `signApprox_Vq` of `FewRunsUncond`. It gives the linear
form bound `2^L ≤ 4 k^341 (2^L − 3^k)` for `k ≥ 2^100`, and then the Simons–de Weger bound
`runs_bound_of_min` shows that such a cycle has at least `200` odd runs.

Together with the earlier ranges, every nontrivial positive `C`-cycle has an odd `T`-orbit minimum
`m ≥ 2^24` with at least `18` odd runs per lap (and in every period window), at least `29` when
`k ≥ 225644606`, and at least `42` when `k ≥ 10^11`. A general cycle may still have arbitrarily
many odd runs; nothing here bounds the number of odd runs of a general cycle.

## Main results

- `linFormHyp_uncond`: `LinFormHyp (2^100) 2 341`, i.e. for `k ≥ 2^100` and `3^k < 2^L`,
  `2^L ≤ 4 k^341 (2^L − 3^k)`.
- `two_pow_tail`: `5(351 + 341e)·8^199 < 3·5^199·2^e` for `e ≥ 167`.
- `runs_tail_uncond`: the odd orbit minimum `m` of a `T`-cycle with `S_L(m) ≥ K1big` has
  `oddRuns L m ≥ 200`.
- `runs_ge_18_uncond`, `runs_ge_29_uncond`, `runs_ge_42_uncond`: for an odd `m ≥ 2^24`, minimal on
  its `T`-orbit, and every period `L`, `oddRuns L m ≥ 18`; `≥ 29` unless `S_L(m) < 225644606`;
  and `≥ 42` if `S_L(m) ≥ 10^11`.
- `state_of_the_art_uncond`, `nontrivial_C_cycle_runs_uncond`: the corresponding statements for
  cycles of the Collatz map `C`.

## References

- J. L. Simons, B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the
  3n+1-problem*, Acta Arith. 117 (2005), 51–70.
- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
  Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
-/

namespace Collatz
open CollatzProof

/-! ### A linear form bound -/

/-- Polynomial linear form bound: for `k ≥ 2^100` and `3^k < 2^L`,
`2^L ≤ 2^2·k^341·(2^L − 3^k)`. It instantiates `irrMeasHyp_of_signApprox` with the witness
`signApprox_Vq` of `FewRunsUncond`, then applies `linFormHyp_of_irrMeas`. -/
theorem linFormHyp_uncond : LinFormHyp (2^100) 2 341 := by
  have h := irrMeasHyp_of_signApprox (a := 74) (b := 37) (c := 46) (d := 2) (t := 119)
    (Q0 := 2^100) (by norm_num) signApprox_Vq (by norm_num) (by norm_num)
    (by rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h2 := linFormHyp_of_irrMeas (by norm_num) (by norm_num) h
  exact h2

/-! ### Cycles with many odd steps -/

/-- The induction step of `two_pow_tail`, kept separate to avoid unfolding large numerals. -/
theorem tail_step {u v w : ℕ} (h1 : v ≤ u) (ih : u < w) : u + v < w * 2 := by omega

/-- `5(351+341e)·8^199 < 3·5^199·2^e` for every `e ≥ 167` (base case by `norm_num`, margin
`≈ 2^15`; the step doubles the right side and adds at most the left side). -/
theorem two_pow_tail (e : ℕ) (he : 167 ≤ e) : 5 * (351 + 341*e) * 8^199 < 3 * 5^199 * 2^e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    have h1 : 5 * 341 * 8^199 ≤ 5 * (351 + 341*e) * 8^199 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have e1 : 5 * (351 + 341*(e+1)) * 8^199 = 5 * (351 + 341*e) * 8^199 + 5 * 341 * 8^199 := by
      ring
    rw [e1, pow_succ 2 e, ← mul_assoc]
    exact tail_step h1 ih

/-- If `m` is odd and minimal on its `T`-orbit, `L > 0`, `T^[L] m = m` and `k = S_L(m) ≥ K1big`,
then the cycle of `m` has at least `200` odd runs in the window `L`. The proof uses the gap
`2^L ≤ 2^{2+341(e+1)}(2^L − 3^k)` with `e = ⌊log₂ k⌋ ≥ 167` from `linFormHyp_uncond`, then
`runs_bound_of_min` and `two_pow_tail`. -/
theorem runs_tail_uncond {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (hK : K1big ≤ oddSteps L m) : 200 ≤ oddRuns L m := by
  by_contra hr
  push Not at hr
  have hm0 : 0 < m := by omega
  have h3 := three_pow_lt_two_pow_of_cycle hm0 hL hc
  set k := oddSteps L m with hkdef
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0] at hK; norm_num [K1big] at hK
  set e := Nat.log 2 k with hedef
  have hle : 2^e ≤ k := Nat.pow_log_le_self 2 hk0
  have hlt : k < 2^(e+1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have he : 167 ≤ e := by
    by_contra hcon
    push Not at hcon
    have : 2^(e+1) ≤ 2^167 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hK2 : (2:ℕ)^167 ≤ K1big := by norm_num [K1big]
    omega
  have hk100 : 2^100 ≤ k := le_trans (by norm_num [K1big]) hK
  have hlin := linFormHyp_uncond k L hk100 h3
  have hkp : k^341 ≤ 2^(341*(e+1)) := by
    rw [show 341*(e+1) = (e+1)*341 from Nat.mul_comm _ _, pow_mul]
    exact Nat.pow_le_pow_left hlt.le _
  have hgap : 2^L ≤ 2^(2 + 341*(e+1)) * (2^L - 3^k) := by
    calc 2^L ≤ 2^2 * k^341 * (2^L - 3^k) := hlin
      _ ≤ 2^2 * 2^(341*(e+1)) * (2^L - 3^k) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkp)
      _ = 2^(2 + 341*(e+1)) * (2^L - 3^k) := by rw [pow_add]
  have ht : oddRuns L m ≤ 2^8 := by norm_num; omega
  have rb := runs_bound_of_min (s := 2 + 341*(e+1)) (t := 8) hodd hL hc hmin h3 hgap ht
  have hW := three_W_add (oddRuns L m)
  have tail := two_pow_tail e he
  set r := oddRuns L m with hrdef
  obtain ⟨j, hj⟩ : ∃ j, 199 = r + j := ⟨199 - r, by omega⟩
  have hs : 2 + 341*(e+1) + 8 = 351 + 341*e := by ring
  rw [hs] at rb
  set A := 5 * (351 + 341*e) with hA
  have hApos : 0 < A := by positivity
  -- 3*5^r*k ≤ A*(3 W r) < A*8^r
  have s1 : 3 * (5^r * k) < A * 8^r := by
    have h5 : 0 < 5^r := by positivity
    calc 3 * (5^r * k) ≤ 3 * (A * W r) := Nat.mul_le_mul_left _ rb
      _ = A * (3 * W r) := by ring
      _ < A * 8^r := Nat.mul_lt_mul_of_pos_left (by omega) hApos
  have s2 : 3 * (5^r * k) * 5^j < A * 8^r * 5^j :=
    Nat.mul_lt_mul_of_pos_right s1 (by positivity)
  have s3 : A * 8^r * 5^j ≤ A * 8^r * 8^j :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)
  have e5 : 3 * (5^r * k) * 5^j = 3 * 5^199 * k := by rw [hj, pow_add]; ring
  have e8 : A * 8^r * 8^j = A * 8^199 := by rw [hj, pow_add]; ring
  have s4 : 3 * 5^199 * 2^e ≤ 3 * 5^199 * k := Nat.mul_le_mul_left _ hle
  rw [e5] at s2; rw [e8] at s3
  omega

/-! ### Run bounds for every number of odd steps -/

/-- The three run bounds at once; see `runs_ge_18_uncond`, `runs_ge_29_uncond` and
`runs_ge_42_uncond`. -/
private theorem runs_ge_18_uncond_aux {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) :
    18 ≤ oddRuns L m ∧ (29 ≤ oddRuns L m ∨ oddSteps L m < 225644606) ∧
      (10^11 ≤ oddSteps L m → 42 ≤ oddRuns L m) := by
  have A := runs_ge_29_K1big hodd h24 hmin hL hc
  have B := runs_ge_18_K1big hodd h24 hmin hL hc
  rcases le_or_gt K1big (oddSteps L m) with hK | hK
  · have := runs_tail_uncond hodd hmin hL hc hK
    exact ⟨by omega, Or.inl (by omega), fun _ => by omega⟩
  · refine ⟨by omega, by omega, fun h ↦ runs_ge_42 hodd hmin hL hc h hK⟩

/-- For an odd `m ≥ 2^24`, minimal on its `T`-orbit, and every `L > 0` with `T^[L] m = m`,
`oddRuns L m ≥ 18`. -/
theorem runs_ge_18_uncond {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) : 18 ≤ oddRuns L m :=
  (runs_ge_18_uncond_aux hodd h24 hmin hL hc).1

/-- For an odd `m ≥ 2^24`, minimal on its `T`-orbit, and every `L > 0` with `T^[L] m = m`,
`oddRuns L m ≥ 29` or `S_L(m) < 225644606`. -/
theorem runs_ge_29_uncond {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) :
    29 ≤ oddRuns L m ∨ oddSteps L m < 225644606 :=
  (runs_ge_18_uncond_aux hodd h24 hmin hL hc).2.1

/-- For an odd `m ≥ 2^24`, minimal on its `T`-orbit, and every `L > 0` with `T^[L] m = m`, if
`S_L(m) ≥ 10^11` then `oddRuns L m ≥ 42`. -/
theorem runs_ge_42_uncond {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) (hk : 10^11 ≤ oddSteps L m) :
    42 ≤ oddRuns L m :=
  (runs_ge_18_uncond_aux hodd h24 hmin hL hc).2.2 hk

/-- Under the hypotheses of `runs_ge_18_uncond`, `3 ≤ oddRuns L m` for every period `L > 0`. -/
theorem runs_ge_3_uncond {m L : ℕ} (hodd : m % 2 = 1) (h24 : 2^24 ≤ m)
    (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L) (hc : T^[L] m = m) : 3 ≤ oddRuns L m := by
  have := runs_ge_18_uncond hodd h24 hmin hL hc; omega

/-! ### Cycles of the Collatz map -/

/-- The conclusion of `state_of_the_art` with its final disjunction replaced by
`18 ≤ oddRuns L m`. -/
theorem state_of_the_art_uncond (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m L a b, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < a ∧ 0 < b ∧ oddSteps L m = 665*a + 11611*b ∧ L = 1054*a + 18403*b ∧
      12276 ≤ oddSteps L m ∧ 19457 ≤ L ∧ 18 ≤ oddRuns L m := by
  obtain ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ :=
    state_of_the_art n hn ℓ hℓ h hne
  exact ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    runs_ge_18_uncond h1 h2 h6 h4 h5⟩

/-- A positive `C`-cycle point `n ∉ {1, 2, 4}` yields an odd `T`-orbit minimum `m` with
`2^24 ≤ m ≤ n` and minimal period `P`, such that the lap has at least `18` odd runs, at least
`29` unless `S_P(m) < 225644606`, at least `62` unless `S_P(m) ≥ 190537`, and at least `42`
whenever `S_P(m) ≥ 10^11`. -/
theorem nontrivial_C_cycle_runs_uncond (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < Function.minimalPeriod T m ∧ T^[Function.minimalPeriod T m] m = m ∧
      18 ≤ oddRuns (Function.minimalPeriod T m) m ∧
      (29 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        oddSteps (Function.minimalPeriod T m) m < 225644606) ∧
      (62 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        190537 ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (10^11 ≤ oddSteps (Function.minimalPeriod T m) m →
        42 ≤ oddRuns (Function.minimalPeriod T m) m) := by
  obtain ⟨m, h1, h2, h3, h6, hP, hPc, -, -, h62⟩ :=
    state_of_the_art_runs_minimalPeriod_K1big n hn ℓ hℓ h hne
  exact ⟨m, h1, h2, h3, h6, hP, hPc, runs_ge_18_uncond h1 h2 h6 hP hPc,
    runs_ge_29_uncond h1 h2 h6 hP hPc, h62, fun hk ↦ runs_ge_42_uncond h1 h2 h6 hP hPc hk⟩

/-! ### Examples -/

-- The linear form bound is available as a term.
example : LinFormHyp (2^100) 2 341 := linFormHyp_uncond

end Collatz
