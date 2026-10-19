/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import OneCircuit
import TwoCircuit
import Mathlib.Data.Nat.Log

/-!
# The 1- and 2-circuit theorems for all `k` from a linear-forms hypothesis

The kernel certificates of `OneCircuit` and `TwoCircuit` rule out nontrivial 1-circuits and
2-circuits with fewer than `100000` odd steps. This file extends both results to all `k`, assuming
a lower bound on `2^L − 3^k`, that is, an effective irrationality measure for `log 3 / log 2`.
Such bounds are known (Rhin, and later work), but they are not proved here: every result about
circuits in this file assumes the hypothesis `TwoCircHyp 100000` or `LinFormHyp K₀ c μ`.

The hypothesis `TwoCircHyp K₀` is tailored to the circuit argument. The hypothesis
`LinFormHyp K₀ c μ` is a polynomial irrationality measure stated in integers, and we show that it
implies `TwoCircHyp 100000` when `K₀ ≤ 100000` and `8(c + 17μ + 2) ≤ 2^16`, for example for
`c = 100`, `μ = 14`. Whether `LinFormHyp 100000 100 14` follows from the published measures is not
checked here. The hypothesis `LinFormHyp 0 c μ` is false for `μ ≥ 1` (`linFormHyp_zero_false`),
so only instances with large `K₀` are meaningful.

The circuit theorems here are stated for sequences that start at the beginning of an odd run.
Versions for arbitrary cycle points are `few_runs_cycle_trivial_of_linForm` and
`few_runs_cycle_trivial_of_linForm_100000` in `RunsBridge`.

## Main definitions

- `TwoCircHyp K₀`: for `k ≥ K₀` and `3^k < 2^L`,
  `2^L (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋}) ≤ 2^{k+1} (2^L − 3^k)`, roughly
  `2^L − 3^k ≥ 2^L (√3/2)^k / 2`.
- `LinFormHyp K₀ c μ`: for `k ≥ K₀` and `3^k < 2^L`, `2^L ≤ 2^c k^μ (2^L − 3^k)`.

## Main results

- `one_circuit_eq_one_of_hyp`, `two_circuit_eq_one_of_hyp`: under `TwoCircHyp 100000`, every
  1-circuit and every 2-circuit has `m = 1`.
- `twoCircHyp_of_linForm`: `LinFormHyp K₀ c μ` implies `TwoCircHyp 100000` when `K₀ ≤ 100000` and
  `8(c + 17μ + 2) ≤ 2^16`.
- `one_circuit_eq_one_of_linForm`, `two_circuit_eq_one_of_linForm`: under such a `LinFormHyp`,
  every 1-circuit and every 2-circuit has `m = 1`.
- `linFormHyp_zero_false`: `LinFormHyp 0 c μ` fails for `μ ≥ 1`.

## References

- R. P. Steiner, *A theorem on the Syracuse problem*, in Proc. 7th Manitoba Conference on
  Numerical Mathematics and Computing (1977), 553–559.
- J. L. Simons, *On the nonexistence of 2-cycles for the 3x+1 problem*, Math. Comp. 74 (2005),
  1565–1572.
- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, in Séminaire de Théorie
  des Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
-/

namespace Collatz

open CollatzProof

/-! ### Circuits under a tailored linear-form bound -/

/-- A linear-form lower bound tailored to circuits: for all `k ≥ K0` and all `L` with
`3^k < 2^L`, `2^L (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋}) ≤ 2^{k+1} (2^L − 3^k)`. It follows from effective
irrationality measures of `log 3 / log 2`, which are not formalized here. -/
def TwoCircHyp (K0 : ℕ) : Prop :=
  ∀ k L : ℕ, K0 ≤ k → 3^k < 2^L → 2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k)

/-- Under `TwoCircHyp 100000`, there is no 1-circuit with `k ≥ 100000`. -/
theorem one_circuit_false_of_hyp {m k l : ℕ} (H : TwoCircHyp 100000) (h : IsOneCircuit m k l)
    (hk : 100000 ≤ k) : False := by
  have s2 := one_circuit_size h
  have s3 := one_circuit_mod_eq_zero h
  have hl := h.2.1
  have hQ : 2 ≤ 2^l := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^l := Nat.pow_le_pow_right (by norm_num) hl
  have hD : 2^(k+l) - 3^k ≤ 2^l - 1 :=
    Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero s3)
  have hH := H k (k+l) hk s2
  have hS : 2 ≤ 2^(k/2+1) + 3^(k/2) := by
    have : 2 ≤ 2^(k/2+1) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(k/2+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_add_right this
  have e1 : 2^(k+l) * 2 = 2^(k+1) * 2^l := by rw [← pow_succ, ← pow_add]; ring_nf
  set P := 2^(k+1)
  set Q := 2^l
  set N := 2^(k+l)
  set D := N - 3^k
  have a1 : N * 2 ≤ N * (2^(k/2+1) + 3^(k/2)) := Nat.mul_le_mul_left _ hS
  have a2 : P * D ≤ P * (Q - 1) := Nat.mul_le_mul_left _ hD
  have hP : 0 < P := by positivity
  have a3 : P * (Q - 1) < P * Q := Nat.mul_lt_mul_of_pos_left (by omega) hP
  omega

/-- Under `TwoCircHyp 100000`, every 1-circuit has `m = 1`, with no bound on `k`. -/
theorem one_circuit_eq_one_of_hyp {m k l : ℕ} (H : TwoCircHyp 100000)
    (h : IsOneCircuit m k l) : m = 1 := by
  rcases Nat.lt_or_ge k 100000 with hk | hk
  · exact one_circuit_eq_one h hk
  · exact (one_circuit_false_of_hyp H h hk).elim

/-- Under `TwoCircHyp 100000`, there is no 2-circuit with `k2 ≤ k1` and `k1 + k2 ≥ 100000`. -/
theorem two_circuit_false_of_hyp_le {m k1 l1 k2 l2 : ℕ} (H : TwoCircHyp 100000)
    (h : IsTwoCircuit m k1 l1 k2 l2) (hk : k2 ≤ k1) (hK : 100000 ≤ k1 + k2) : False := by
  have hsz := two_circuit_size hk h
  have hodd := two_circuit_odd h
  have hL : 0 < k1+l1+k2+l2 := by have := h.1; omega
  have H3 := three_pow_lt_two_pow_of_cycle (by omega) hL h.2.2.2.2.2.2.2.2
  rw [two_circuit_oddSteps h] at H3
  have hH := H (k1+k2) (k1+l1+k2+l2) hK H3
  generalize 2^(k1+l1+k2+l2) = N at *
  generalize 3^(k1+k2) = K at *
  generalize 2^(k1+k2+1) = P at *
  generalize 2^((k1+k2)/2+1) + 3^((k1+k2)/2) = S at *
  obtain ⟨D, rfl⟩ : ∃ D, N = D + K := ⟨N - K, by omega⟩
  rw [Nat.add_sub_cancel] at hH
  nlinarith

/-- Under `TwoCircHyp 100000`, every 2-circuit has `m = 1`, with no bound on `k`. -/
theorem two_circuit_eq_one_of_hyp {m k1 l1 k2 l2 : ℕ} (H : TwoCircHyp 100000)
    (h : IsTwoCircuit m k1 l1 k2 l2) : m = 1 := by
  rcases Nat.lt_or_ge (k1 + k2) 100000 with hk | hk
  · exact two_circuit_eq_one h hk
  · rcases Nat.le_total k2 k1 with h21 | h12
    · exact (two_circuit_false_of_hyp_le H h h21 hk).elim
    · exact (two_circuit_false_of_hyp_le H (two_circuit_rotate h) h12 (by omega)).elim

/-! ### Reduction to a polynomial irrationality measure -/

/-- A polynomial irrationality measure of `log 3 / log 2` in integer form: for `k ≥ K0` and
`3^k < 2^L`, `2^L ≤ 2^c k^μ (2^L − 3^k)`. It is not proved here. -/
def LinFormHyp (K0 c μ : ℕ) : Prop :=
  ∀ k L : ℕ, K0 ≤ k → 3^k < 2^L → 2^L ≤ 2^c * k^μ * (2^L - 3^k)

/-- `3^h 2^{⌊h/4⌋} ≤ 4^h` (since `3^4·2 = 162 ≤ 256 = 4^4`). -/
theorem three_pow_mul_two_pow_le (h : ℕ) : 3^h * 2^(h/4) ≤ 4^h := by
  have hd := Nat.div_add_mod h 4
  set t := h / 4
  set s := h % 4
  have hs : s < 4 := Nat.mod_lt _ (by norm_num)
  rw [← hd]
  have e1 : 3^(4*t+s) * 2^t = 162^t * 3^s := by
    rw [pow_add, pow_mul, show (162:ℕ) = 3^4 * 2 by norm_num, mul_pow]; ring
  have e2 : 4^(4*t+s) = 256^t * 4^s := by
    rw [pow_add, pow_mul]; norm_num
  rw [e1, e2]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) _)
    (Nat.pow_le_pow_left (by norm_num) _)

/-- If `8(c + μ(⌊log₂ k⌋ + 1) + 2) ≤ k`, then
`2^c k^μ (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋}) < 2^{k+1}`. -/
theorem growth {c μ k : ℕ} (hk : 8 * (c + μ * (Nat.log 2 k + 1) + 2) ≤ k) :
    2^c * k^μ * (2^(k/2+1) + 3^(k/2)) < 2^(k+1) := by
  set j := Nat.log 2 k
  set E := c + μ * (j + 1)
  have hkj : k < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hkμ : k^μ ≤ 2^(μ*(j+1)) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hkj.le _
  have hcE : 2^c * k^μ ≤ 2^E := by
    rw [show E = c + μ*(j+1) from rfl, pow_add]; exact Nat.mul_le_mul_left _ hkμ
  set h := k / 2
  have h2h : 2 * h ≤ k := Nat.mul_div_le k 2
  have h23 : 2^h ≤ 3^h := Nat.pow_le_pow_left (by norm_num) h
  have h3pos : 1 ≤ 3^h := Nat.one_le_pow _ _ (by norm_num)
  have hS : 2^(h+1) + 3^h < 4 * 3^h := by rw [pow_succ]; omega
  have h4 : h / 4 = k / 8 := by rw [Nat.div_div_eq_div_mul]
  have hE2 : E + 2 ≤ h / 4 := by
    rw [h4, Nat.le_div_iff_mul_le (by norm_num)]; omega
  have hEpos : 0 < 2^E := by positivity
  calc 2^c * k^μ * (2^(h+1) + 3^h) ≤ 2^E * (2^(h+1) + 3^h) := Nat.mul_le_mul_right _ hcE
    _ < 2^E * (4 * 3^h) := Nat.mul_lt_mul_of_pos_left hS hEpos
    _ = 2^(E+2) * 3^h := by rw [pow_add]; ring
    _ ≤ 2^(h/4) * 3^h := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hE2)
    _ = 3^h * 2^(h/4) := by ring
    _ ≤ 4^h := three_pow_mul_two_pow_le h
    _ = 2^(2*h) := by rw [pow_mul]; norm_num
    _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) h2h
    _ < 2^(k+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- If `8(c+17μ+2) ≤ 2^16` then `8(c + μ(⌊log₂ k⌋+1) + 2) ≤ k` for every `k ≥ 2^16`. -/
theorem log_cond {c μ : ℕ} (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (k : ℕ) (hk : 2^16 ≤ k) :
    8 * (c + μ * (Nat.log 2 k + 1) + 2) ≤ k := by
  have hk0 : k ≠ 0 := by omega
  have hj : 16 ≤ Nat.log 2 k := Nat.le_log_of_pow_le (by norm_num) hk
  have hjk : 2^(Nat.log 2 k) ≤ k := Nat.pow_log_le_self 2 hk0
  have claim : ∀ j, 16 ≤ j → 8 * (c + μ * (j + 1) + 2) ≤ 2^j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simpa [mul_comm] using h0
    | succ j hj ih =>
      have hp : 2^16 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
      have e : 2^(j+1) = 2 * 2^j := by rw [pow_succ]; ring
      have e2 : μ * (j + 1 + 1) = μ * (j + 1) + μ := by ring
      rw [e, e2]
      omega
  exact (claim _ hj).trans hjk

/-- `LinFormHyp K0 c μ` with `K0 ≤ 100000` and `8(c + 17μ + 2) ≤ 2^16` implies
`TwoCircHyp 100000`. -/
theorem twoCircHyp_of_linForm {K0 c μ : ℕ} (hK0 : K0 ≤ 100000)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K0 c μ) : TwoCircHyp 100000 := by
  intro k L hk h3
  have hL := H k L (by omega) h3
  have hg := growth (log_cond h0 k (by norm_num; omega))
  set S := 2^(k/2+1) + 3^(k/2)
  set D := 2^L - 3^k
  calc 2^L * S ≤ (2^c * k^μ * D) * S := Nat.mul_le_mul_right _ hL
    _ = (2^c * k^μ * S) * D := by ring
    _ ≤ 2^(k+1) * D := Nat.mul_le_mul_right _ hg.le

/-- Under `LinFormHyp K0 c μ` with `K0 ≤ 100000` and `8(c + 17μ + 2) ≤ 2^16`, every 1-circuit
has `m = 1`. -/
theorem one_circuit_eq_one_of_linForm {K0 c μ : ℕ} (hK0 : K0 ≤ 100000)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K0 c μ) {m k l : ℕ}
    (h : IsOneCircuit m k l) : m = 1 :=
  one_circuit_eq_one_of_hyp (twoCircHyp_of_linForm hK0 h0 H) h

/-- Under `LinFormHyp K0 c μ` with `K0 ≤ 100000` and `8(c + 17μ + 2) ≤ 2^16`, every 2-circuit
has `m = 1`. -/
theorem two_circuit_eq_one_of_linForm {K0 c μ : ℕ} (hK0 : K0 ≤ 100000)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K0 c μ) {m k1 l1 k2 l2 : ℕ}
    (h : IsTwoCircuit m k1 l1 k2 l2) : m = 1 :=
  two_circuit_eq_one_of_hyp (twoCircHyp_of_linForm hK0 h0 H) h

/-- `LinFormHyp 0 c μ` is false for `μ ≥ 1` (take `k = 0`, `L = 1`), so instances with small
`K0` are vacuous as hypotheses. -/
theorem linFormHyp_zero_false {c μ : ℕ} (hμ : 1 ≤ μ) : ¬ LinFormHyp 0 c μ := by
  intro H
  have := H 0 1 le_rfl (by norm_num)
  rw [zero_pow (by omega)] at this
  simp at this

/-- Under `LinFormHyp 100000 100 14`, every 1-circuit has `m = 1`. -/
theorem one_circuit_eq_one_of_linForm_100000 (H : LinFormHyp 100000 100 14) {m k l : ℕ}
    (h : IsOneCircuit m k l) : m = 1 :=
  one_circuit_eq_one_of_linForm le_rfl (by norm_num) H h

/-- Under `LinFormHyp 100000 100 14`, every 2-circuit has `m = 1`. -/
theorem two_circuit_eq_one_of_linForm_100000 (H : LinFormHyp 100000 100 14)
    {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) : m = 1 :=
  two_circuit_eq_one_of_linForm le_rfl (by norm_num) H h

/-! ### Examples -/

-- The numeric side condition holds for `μ = 14`, `c = 100`.
example : 8 * (100 + 17*14 + 2) ≤ 2^16 := by norm_num


end Collatz
