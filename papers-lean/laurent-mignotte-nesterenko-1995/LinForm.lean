import OneCircuit
import TwoCircuit
import Mathlib.Data.Nat.Log

/-!
# Conditional all-`k` 1- and 2-circuit theorems from a linear-forms hypothesis

**CONDITIONAL.**  Everything in the second half of this file assumes an *unformalized*
hypothesis about how well `log 3 / log 2` can be approximated by rationals (a lower bound on
`2^L − 3^k`).  Such bounds are true in the literature (Rhin 1987 and later effective
irrationality measures of `log 3/log 2`), but they are **not proved here**.  These are
therefore *not* unconditional Steiner (1977) / Simons (2005) theorems.

* `TwoCircHyp K0`: for all `k ≥ K0` and `L` with `3^k < 2^L`,
  `2^L (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋}) ≤ 2^{k+1} (2^L − 3^k)`, i.e. roughly
  `2^L − 3^k ≥ 2^L (√3/2)^k / 2`.
* T1: `TwoCircHyp 100000 ⇒` every 1-circuit and every 2-circuit has `m = 1` (all `k`),
  combining with the kernel certificates for `k < 10^5`.
* `LinFormHyp K0 c μ`: for `k ≥ K0` and `3^k < 2^L`, `2^L ≤ 2^c k^μ (2^L − 3^k)`
  (a polynomial irrationality measure, stated in integers).
* T2: if `K0 ≤ 100000` and `8(c + 17μ + 2) ≤ 2^16`, then `LinFormHyp K0 c μ ⇒ TwoCircHyp 100000`.
  Example: `μ = 14`, `c = 100`.

**Caveats.**
* `LinFormHyp K0 c μ` is **false** for `K0 = 0` whenever `μ ≥ 1`: at `k = 0`, `L = 1` we have
  `3^0 < 2^1` but the right side is `2^c · 0^μ · 1 = 0 < 2` (`linFormHyp_zero_false`).  So
  small-`K0` instances are vacuous as hypotheses; the intended instance is `K0 = 100000`,
  e.g. `LinFormHyp 100000 100 14`.
* The constants `(c, μ) = (100, 14)` are only checked against the **numeric side condition**
  `8(c+17μ+2) ≤ 2^16`.  Nobody has checked against the literature (Rhin 1987, Wu–Wang 2014,
  Hata) [`IrrMeasureReal`: Wu–Wang 2014, J. Number Theory, DOI 10.1016/j.jnt.2014.03.007, 'On the irrationality measure of log 3', concerns log 3, NOT log 3/log 2] that `LinFormHyp 100000 100 14` actually holds.  That is the subject of the next
  scoping round.
* The circuit theorems here are **phased** (the sequence starts at an odd-run start).  The
  rotation-free, cycle-level versions are in `RunsBridge.lean`
  (`few_runs_cycle_trivial_of_linForm`, `few_runs_cycle_trivial_of_linForm_100000`).
-/

namespace Collatz
open CollatzProof

/-- **Unproved hypothesis** (tailored linear-form lower bound). For all `k ≥ K0` and all `L`
with `3^k < 2^L`: `2^L (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋}) ≤ 2^{k+1} (2^L − 3^k)`.
NOT proved; it follows from known effective irrationality measures of `log 3/log 2`
(Rhin 1987 and later), which are not formalized. Theorems using it are conditional. -/
def TwoCircHyp (K0 : ℕ) : Prop :=
  ∀ k L : ℕ, K0 ≤ k → 3^k < 2^L → 2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k)

/-- CONDITIONAL on `TwoCircHyp 100000`: no 1-circuit with `k ≥ 100000`. -/
theorem one_circuit_false_of_hyp {m k l : ℕ} (H : TwoCircHyp 100000) (h : IsOneCircuit m k l)
    (hk : 100000 ≤ k) : False := by
  obtain ⟨-, s2, s3⟩ := one_circuit_size h
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

/-- CONDITIONAL on `TwoCircHyp 100000`: every 1-circuit has `m = 1` (no bound on `k`). -/
theorem one_circuit_eq_one_of_hyp {m k l : ℕ} (H : TwoCircHyp 100000) (h : IsOneCircuit m k l) :
    m = 1 := by
  rcases Nat.lt_or_ge k 100000 with hk | hk
  · exact one_circuit_eq_one h hk
  · exact (one_circuit_false_of_hyp H h hk).elim

/-- CONDITIONAL on `TwoCircHyp 100000`: no 2-circuit with `k2 ≤ k1`, `k1+k2 ≥ 100000`. -/
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

/-- CONDITIONAL on `TwoCircHyp 100000`: every 2-circuit has `m = 1` (no bound on `k`). -/
theorem two_circuit_eq_one_of_hyp {m k1 l1 k2 l2 : ℕ} (H : TwoCircHyp 100000)
    (h : IsTwoCircuit m k1 l1 k2 l2) : m = 1 := by
  rcases Nat.lt_or_ge (k1 + k2) 100000 with hk | hk
  · exact two_circuit_eq_one h hk
  · rcases Nat.le_total k2 k1 with h21 | h12
    · exact (two_circuit_false_of_hyp_le H h h21 hk).elim
    · exact (two_circuit_false_of_hyp_le H (two_circuit_rotate h) h12 (by omega)).elim

/-! ## T2: reduction to a polynomial irrationality measure -/

/-- **Unproved hypothesis** (polynomial irrationality measure of `log 3/log 2`, integer form):
for `k ≥ K0` and `3^k < 2^L`, `2^L ≤ 2^c k^μ (2^L − 3^k)`. NOT proved here. -/
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
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) _) (Nat.pow_le_pow_left (by norm_num) _)

/-- Growth: if `8(c + μ(⌊log₂ k⌋+1) + 2) ≤ k` then `2^c k^μ (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋}) < 2^{k+1}`. -/
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

/-- CONDITIONAL reduction: `LinFormHyp K0 c μ` with `K0 ≤ 100000` and `8(c+17μ+2) ≤ 2^16`
implies `TwoCircHyp 100000`. (`LinFormHyp` is an unformalized hypothesis.) -/
theorem twoCircHyp_of_linForm {K0 c μ : ℕ} (hK0 : K0 ≤ 100000) (h0 : 8 * (c + 17*μ + 2) ≤ 2^16)
    (H : LinFormHyp K0 c μ) : TwoCircHyp 100000 := by
  intro k L hk h3
  have hL := H k L (by omega) h3
  have hg := growth (log_cond h0 k (by norm_num; omega))
  set S := 2^(k/2+1) + 3^(k/2)
  set D := 2^L - 3^k
  calc 2^L * S ≤ (2^c * k^μ * D) * S := Nat.mul_le_mul_right _ hL
    _ = (2^c * k^μ * S) * D := by ring
    _ ≤ 2^(k+1) * D := Nat.mul_le_mul_right _ hg.le

/-- CONDITIONAL on the unformalized `LinFormHyp K0 c μ` (`K0 ≤ 100000`, `8(c+17μ+2) ≤ 2^16`):
there are no nontrivial 1-circuits and no nontrivial 2-circuits. -/
theorem no_circuits_of_linForm {K0 c μ : ℕ} (hK0 : K0 ≤ 100000) (h0 : 8 * (c + 17*μ + 2) ≤ 2^16)
    (H : LinFormHyp K0 c μ) :
    (∀ m k l, IsOneCircuit m k l → m = 1) ∧
      (∀ m k1 l1 k2 l2, IsTwoCircuit m k1 l1 k2 l2 → m = 1) :=
  have H' := twoCircHyp_of_linForm hK0 h0 H
  ⟨fun _ _ _ h => one_circuit_eq_one_of_hyp H' h,
   fun _ _ _ _ _ h => two_circuit_eq_one_of_hyp H' h⟩

/-- Numeric side condition for `μ = 14`, `c = 100`. -/
example : 8 * (100 + 17*14 + 2) ≤ 2^16 := by norm_num

/-- `LinFormHyp 0 c μ` is **false** for `μ ≥ 1` (take `k = 0`, `L = 1`).  Small-`K0`
instances are vacuous hypotheses; use `K0 = 100000`. -/
theorem linFormHyp_zero_false {c μ : ℕ} (hμ : 1 ≤ μ) : ¬ LinFormHyp 0 c μ := by
  intro H
  have := H 0 1 le_rfl (by norm_num)
  rw [zero_pow (by omega)] at this
  simp at this

/-- Named instance, CONDITIONAL on the unformalized `LinFormHyp 100000 100 14` (constants not
checked against the literature): no nontrivial 1-circuits or 2-circuits (phased statement;
see `RunsBridge.few_runs_cycle_trivial_of_linForm_100000` for the cycle-level form). -/
theorem no_circuits_of_linForm_100000 (H : LinFormHyp 100000 100 14) :
    (∀ m k l, IsOneCircuit m k l → m = 1) ∧
      (∀ m k1 l1 k2 l2, IsTwoCircuit m k1 l1 k2 l2 → m = 1) :=
  no_circuits_of_linForm le_rfl (by norm_num) H

end Collatz

#print axioms Collatz.twoCircHyp_of_linForm
#print axioms Collatz.no_circuits_of_linForm
#print axioms Collatz.one_circuit_eq_one_of_hyp
#print axioms Collatz.two_circuit_eq_one_of_hyp
#print axioms Collatz.linFormHyp_zero_false
#print axioms Collatz.no_circuits_of_linForm_100000
