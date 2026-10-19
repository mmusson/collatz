/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Collatz.StateOfArt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Cycles with at most two odd runs, from a lower bound for linear forms in two logarithms

Laurent, Mignotte and Nesterenko, and later Laurent, give explicit lower bounds for linear forms
in two logarithms. Specialised to `Λ = k log 3 − L log 2`, such a bound gives
`2^L ≤ 2^(1 + 51(⌊log₂ k⌋ + 21)²) (2^L − 3^k)` for `k ≥ 2^20` and `3^k < 2^L`. This quasi-polynomial
gap is enough for the hypothesis `TwoCircHyp 100000` of `LinForm`, and hence for the 1- and
2-circuit theorems of Steiner and Simons for every `k`: every positive `T`-cycle point whose
window has at most two odd runs is `1` or `2`.

The lower bound itself is not formalized. It is stated as the hypothesis `LMNHyp Cst c0 m0`, and
all results after `growth_LMN` assume it. The results are stated for a box of constants
`Cst ≤ 51/2`, `c0 ≤ 1`, `0 ≤ m0 ≤ 21`, which contains the constants `(24.34, 0.14, 21)` of
Laurent–Mignotte–Nesterenko (Cor. 2) and `(25.2, 0.21, 20)` of Laurent (Cor. 1, `m = 20`) and
tolerates small transcription errors. These constants should be checked against the original
papers before relying on the named instances.

A bound of this quasi-polynomial shape, `|Λ| ≥ exp(−C (log k)²)`, does not imply the polynomial
hypothesis `LinFormHyp K c μ` of `LinForm` for large `k`, since `(log k)²` eventually exceeds
`μ log k`. The hypothesis `TwoCircHyp` only needs a gap of size about `(3/4)^{k/2}`, so this file
targets `TwoCircHyp` directly. Nothing here bounds the number of odd runs of a general cycle.

## Main definitions

- `LMNHyp Cst c0 m0`: the two-logarithm lower bound for `k log 3 − L log 2` with constants
  `Cst`, `c0`, `m0`.

## Main results

- `gap_of_LMN`: under `LMNHyp`, for `k ≥ 2^20` and `3^k < 2^L`,
  `2^L ≤ 2^(1 + 51(⌊log₂ k⌋ + 21)²) (2^L − 3^k)`.
- `twoCircAt_of_LMN`, `twoCircHyp_of_LMN`: under `LMNHyp`, the inequality of `TwoCircHyp` holds
  for `k ≥ 2^20`, and `TwoCircHyp 100000` holds (the range `[10^5, 2^20)` is covered
  unconditionally by `gapBelow_225644606`).
- `few_runs_cycle_trivial_of_LMN`: under `LMNHyp`, every positive `T`-cycle point with at most two
  odd runs is `1` or `2`.
- `state_of_the_art_of_LMN`: under `LMNHyp`, the conclusion of `state_of_the_art` holds with at
  least three odd runs.
- `few_runs_cycle_trivial_of_LMN95`, `few_runs_cycle_trivial_of_Laurent08`: the instances with
  the constants of the two papers.

## References

- M. Laurent, M. Mignotte, Yu. Nesterenko, *Formes linéaires en deux logarithmes et déterminants
  d'interpolation*, J. Number Theory 55 (1995), 285–321.
- M. Laurent, *Linear forms in two logarithms and interpolation determinants II*, Acta Arith. 133
  (2008), 325–348.
- R. P. Steiner, *A theorem on the Syracuse problem*, in Proc. 7th Manitoba Conference on
  Numerical Mathematics and Computing (1977), 553–559.
- J. L. Simons, *On the nonexistence of 2-cycles for the 3x+1 problem*, Math. Comp. 74 (2005),
  1565–1572.
-/

namespace Collatz

open CollatzProof

/-! ### The hypothesis -/

/-- The explicit lower bound of Laurent–Mignotte–Nesterenko (Cor. 2) and Laurent (Cor. 1) for
`Λ = k log 3 − L log 2`, specialised to `D = 1`, `α₁ = 2` (`log A₁ = max(h(2), log 2, 1) = 1`,
omitted as a factor), `α₂ = 3` (`log A₂ = max(h(3), log 3, 1) = log 3`),
`b' = b₁/(D log A₂) + b₂/(D log A₁) = L / log 3 + k`:
for all `k, L ≥ 1`, `−Cst · max(log b' + c0, m0)² · log 3 ≤ log |k log 3 − L log 2|`.
The third entry `1/2` of the published maximum is dropped, which is harmless when `m0 ≥ 1/2`.
This is a hypothesis; it is not proved here. -/
def LMNHyp (Cst c0 m0 : ℝ) : Prop :=
  ∀ k L : ℕ, 0 < k → 0 < L →
    -Cst * (max (Real.log ((L:ℝ) / Real.log 3 + k) + c0) m0)^2 * Real.log 3
      ≤ Real.log |(k:ℝ) * Real.log 3 - (L:ℝ) * Real.log 2|

/-! ### The integer gap -/

/-- `8 (1 + 51 (ℓ + 21)²) ≤ 2^ℓ` for `ℓ ≥ 20`. -/
theorem growth_LMN (ℓ : ℕ) (h : 20 ≤ ℓ) : 8 * (1 + 51 * (ℓ + 21)^2) ≤ 2^ℓ := by
  induction ℓ, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : (n+1+21)^2 ≤ 2*(n+21)^2 := by nlinarith
    rw [pow_succ 2 n]; nlinarith

/-- The gap of `gap_of_LMN`, with `ℓ` any natural number such that `k < 2^(ℓ+1)`. The
hypothesis `0 ≤ Cst` is not used. -/
theorem gap_of_LMN_core {Cst c0 m0 : ℝ} (_hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2) (hc0 : c0 ≤ 1)
    (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0) {k L ℓ : ℕ} (hk0 : k ≠ 0)
    (hkl : k < 2^(ℓ+1)) (hL : 3^k < 2^L) :
    2^L ≤ 2^(1 + 51 * (ℓ + 21)^2) * (2^L - 3^k) := by
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp at hL
    · exact h
  rcases lt_or_ge (2*k) L with hA | hB
  · have h1 : 3^k < 4^k := Nat.pow_lt_pow_left (by norm_num) hk0
    have h2 : 2 * 4^k ≤ 2^L := by
      rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ≤ 2^(1 + 51 * (ℓ + 21)^2) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2^L ≤ 2 * (2^L - 3^k) := by omega
    exact h4.trans (Nat.mul_le_mul_right _ h3)
  · generalize hE' : 51 * (ℓ+21)^2 = E'
    have hlog2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog3 : 2/3 ≤ Real.log 3 := by
      have := Real.one_sub_inv_le_log_of_pos (x := 3) (by norm_num); norm_num at this ⊢; linarith
    have hlog3lt : Real.log 3 < 2 * Real.log 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      rw [← this]; exact Real.log_lt_log (by norm_num) (by norm_num)
    set a : ℝ := (2:ℝ)^L with ha_def
    set b : ℝ := (3:ℝ)^k with hb_def
    have hb : 0 < b := by positivity
    have ha : 0 < a := by positivity
    have hab : b < a := by simp only [a, b]; exact_mod_cast hL
    set x := (L:ℝ) * Real.log 2 - k * Real.log 3 with hx_def
    have hla : Real.log a = L * Real.log 2 := Real.log_pow _ _
    have hlb : Real.log b = k * Real.log 3 := Real.log_pow _ _
    have hx : 0 < x := by have := Real.log_lt_log hb hab; linarith
    have hkR : (k:ℝ) < 2^(ℓ+1) := by exact_mod_cast hkl
    have hLR : (L:ℝ) ≤ 2*k := by exact_mod_cast hB
    have hkpos : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hl3pos : 0 < Real.log 3 := by linarith
    have harg_pos : 0 < (L:ℝ)/Real.log 3 + k := by positivity
    have harg : (L:ℝ)/Real.log 3 + k < 2^(ℓ+3) := by
      have h1 : (L:ℝ)/Real.log 3 ≤ 3 * k := by
        rw [div_le_iff₀ hl3pos]; nlinarith
      have : (2:ℝ)^(ℓ+3) = 4 * 2^(ℓ+1) := by ring
      linarith
    have hlogarg : Real.log ((L:ℝ)/Real.log 3 + k) < ℓ + 3 := by
      have := Real.log_lt_log harg_pos harg
      rw [Real.log_pow] at this
      push_cast at this
      have hl0 : (0:ℝ) ≤ ℓ := by positivity
      nlinarith
    set M := max (Real.log ((L:ℝ)/Real.log 3 + k) + c0) m0 with hM_def
    have hM0 : 0 ≤ M := le_trans hm0 (le_max_right _ _)
    have hl0 : (0:ℝ) ≤ ℓ := by positivity
    have hM1 : M ≤ ℓ + 21 := max_le (by linarith) (by linarith)
    have hM2 : M^2 ≤ ((ℓ:ℝ)+21)^2 := pow_le_pow_left₀ hM0 hM1 2
    have hH := H k L (Nat.pos_of_ne_zero hk0) hLpos
    have habs : |(k:ℝ) * Real.log 3 - L * Real.log 2| = x := by
      rw [abs_sub_comm]; exact abs_of_pos hx
    rw [habs] at hH
    have hE'R : ((E':ℕ):ℝ) = 51 * ((ℓ:ℝ)+21)^2 := by rw [← hE']; push_cast; ring
    have key : Cst * M^2 * Real.log 3 ≤ (E':ℝ) * Real.log 2 := by
      rw [hE'R]
      have h1 : Cst * M^2 ≤ 51/2 * ((ℓ:ℝ)+21)^2 := mul_le_mul hC hM2 (sq_nonneg _) (by norm_num)
      have h2 : Cst * M^2 * Real.log 3 ≤ 51/2 * ((ℓ:ℝ)+21)^2 * Real.log 3 :=
        mul_le_mul_of_nonneg_right h1 hl3pos.le
      have h3 : 51/2 * ((ℓ:ℝ)+21)^2 * Real.log 3 ≤ 51/2 * ((ℓ:ℝ)+21)^2 * (2*Real.log 2) :=
        mul_le_mul_of_nonneg_left hlog3lt.le (by positivity)
      linarith
    have hlogx : -((E':ℝ) * Real.log 2) ≤ Real.log x := by
      have : -Cst * M^2 * Real.log 3 = -(Cst * M^2 * Real.log 3) := by ring
      linarith
    set P : ℝ := (2:ℝ)^E' with hP_def
    have hP1 : 1 ≤ P := one_le_pow₀ (by norm_num)
    have hPx : 1 ≤ P * x := by
      have hy : Real.exp (-((E':ℝ) * Real.log 2)) = P⁻¹ := by
        rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
      have hxy : P⁻¹ ≤ x := by
        rw [← hy, ← Real.exp_log hx]; exact Real.exp_le_exp.mpr hlogx
      have hP0 : 0 < P := by positivity
      calc (1:ℝ) = P * P⁻¹ := (mul_inv_cancel₀ hP0.ne').symm
        _ ≤ P * x := mul_le_mul_of_nonneg_left hxy hP0.le
    have hexa : Real.exp x = a / b := by
      rw [show x = Real.log a - Real.log b by linarith, Real.exp_sub, Real.exp_log ha,
        Real.exp_log hb]
    have hbx : b * (1 + x) ≤ a := by
      have := Real.add_one_le_exp x
      rw [hexa] at this
      have : b * (x + 1) ≤ b * (a / b) := mul_le_mul_of_nonneg_left this hb.le
      rw [mul_div_cancel₀ _ hb.ne'] at this; linarith
    have hreal : a ≤ 2 * P * (a - b) := by
      have hab' : 0 ≤ a - b := by linarith
      have e1 : a - b ≤ P * (a - b) := by nlinarith
      have e2 : b ≤ P * (a - b) := by
        calc b = b * 1 := by ring
          _ ≤ b * (P * x) := mul_le_mul_of_nonneg_left hPx hb.le
          _ = P * (b * x) := by ring
          _ ≤ P * (a - b) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hcast : ((2^L : ℕ) : ℝ) ≤ ((2^(1 + E') * (2^L - 3^k) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hL.le]
      push_cast
      rw [pow_add]
      simpa [a, b, P, mul_assoc] using hreal
    exact_mod_cast hcast

/-- Under `LMNHyp`, for `k ≥ 2^20` and `3^k < 2^L`,
`2^L ≤ 2^(1 + 51(⌊log₂ k⌋ + 21)²) (2^L − 3^k)`. -/
theorem gap_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2) (hc0 : c0 ≤ 1)
    (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0) {k L : ℕ} (hk : 2^20 ≤ k)
    (hL : 3^k < 2^L) :
    2^L ≤ 2^(1 + 51 * (Nat.log 2 k + 21)^2) * (2^L - 3^k) :=
  gap_of_LMN_core hC0 hC hc0 hm0 hm1 H (by omega) (Nat.lt_pow_succ_log_self (by norm_num) k)
    hL

/-! ### Circuits and cycles with few odd runs -/

/-- Under `LMNHyp`, the inequality of `TwoCircHyp` holds at every `k ≥ 2^20`. -/
theorem twoCircAt_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2) (hc0 : c0 ≤ 1)
    (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0) {k : ℕ} (hk : 2^20 ≤ k) :
    TwoCircAt k := by
  intro L hL
  set h := k / 2 with hh
  set ℓ := Nat.log 2 k with hℓ
  set E := 1 + 51 * (ℓ + 21)^2 with hE_def
  have h2h : 2 * h ≤ k := Nat.mul_div_le k 2
  have s1 : 2^(h+1) + 3^h ≤ 2 * 3^h := by
    have := two_pow_succ_le_three_pow (h := h) (by omega); omega
  have s2 := three_pow_mul_two_pow_le h
  have s3 : 4^h ≤ 2^k := by
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) h2h
  have hℓ20 : 20 ≤ ℓ := Nat.le_log_of_pow_le (by norm_num) hk
  have hpk : 2^ℓ ≤ k := Nat.pow_log_le_self 2 (by omega)
  have g := growth_LMN ℓ hℓ20
  have hE : E ≤ h / 4 := by
    rw [hh, Nat.div_div_eq_div_mul]
    exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have s4 : 2^E * 3^h ≤ 2^k :=
    calc 2^E * 3^h ≤ 2^(h/4) * 3^h :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hE)
      _ = 3^h * 2^(h/4) := mul_comm _ _
      _ ≤ 4^h := s2
      _ ≤ 2^k := s3
  have G := gap_of_LMN hC0 hC hc0 hm0 hm1 H hk hL
  rw [← hℓ, ← hE_def] at G
  clear_value E
  calc 2^L * (2^(h+1) + 3^h) ≤ (2^E * (2^L - 3^k)) * (2 * 3^h) := Nat.mul_le_mul G s1
    _ = 2 * (2^E * 3^h) * (2^L - 3^k) := by ring
    _ ≤ 2 * 2^k * (2^L - 3^k) := by gcongr
    _ = 2^(k+1) * (2^L - 3^k) := by ring

/-- Under `LMNHyp`, `TwoCircHyp 100000` holds. The range `[10^5, 2^20)` is covered
unconditionally by `gapBelow_225644606`. -/
theorem twoCircHyp_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2) (hc0 : c0 ≤ 1)
    (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0) : TwoCircHyp 100000 := by
  intro k L hk hL
  rcases Nat.lt_or_ge k (2^20) with h | h
  · exact twoCirc_of_gap gapBelow_225644606 hk (by omega) hL
  · exact twoCircAt_of_LMN hC0 hC hc0 hm0 hm1 H h L hL

/-- Under `LMNHyp`, every positive `T`-cycle point (at any phase, for any period `L > 0`) whose
window has at most two odd runs is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2)
    (hc0 : c0 ≤ 1) (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  have HH := twoCircHyp_of_LMN hC0 hC hc0 hm0 hm1 H
  few_runs_cycle_trivial_core hx hL hc hr (fun _ _ _ h _ => one_circuit_eq_one_of_hyp HH h)
    (fun _ _ _ _ _ h _ => two_circuit_eq_one_of_hyp HH h)

/-- Under `LMNHyp`, the conclusion of `state_of_the_art` holds with its final disjunction
strengthened to at least three odd runs. -/
theorem state_of_the_art_of_LMN {Cst c0 m0 : ℝ} (hC0 : 0 ≤ Cst) (hC : Cst ≤ 51/2)
    (hc0 : c0 ≤ 1) (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 21) (H : LMNHyp Cst c0 m0)
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
  rcases few_runs_cycle_trivial_of_LMN hC0 hC hc0 hm0 hm1 H (x := m) (by omega) h4 h5
    (by omega) with e | e <;> omega

/-! ### Instances with published constants -/

/-- Under `LMNHyp 24.34 0.14 21` (the constants of Laurent–Mignotte–Nesterenko, Cor. 2), every
positive `T`-cycle point with at most two odd runs is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_LMN95 (H : LMNHyp 24.34 0.14 21) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_LMN (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) H hx hL hc hr

/-- Under `LMNHyp 25.2 0.21 20` (the constants of Laurent, Cor. 1 with `m = 20`), every positive
`T`-cycle point with at most two odd runs is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_Laurent08 (H : LMNHyp 25.2 0.21 20) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_LMN (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) H hx hL hc hr

end Collatz
