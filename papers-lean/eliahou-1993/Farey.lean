/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import RunsBridge
import Mathlib.Tactic

/-!
# Farey neighbours of `log₂ 3` and lower bounds for `2^L − 3^k`

If `p/q > log₂ 3 > p'/q'` are Farey neighbours, then no `3^k/2^L < 1` with `0 < k < q + q'` is
closer to `1` than `3^q/2^p`. This is the continued-fraction reduction used by Eliahou, proved
here in pure integer arithmetic. One Farey pair together with one large-number check therefore
gives a uniform gap `2^L ≤ 2^s (2^L − 3^k)` for all `0 < k < q + q'`, the property `GapBelow`.

A gap of the form `GapBelow K₁ 30` yields the hypothesis `TwoCircHyp` of `LinForm` on
`[10^5, K₁)`, and hence excludes 1- and 2-circuits with fewer than `K₁` odd steps and nontrivial
`T`-cycles with at most two odd runs and fewer than `K₁` odd steps. We prove `GapBelow 10781274 30`
from the pair `301994/190537 > log₂ 3 > 16785921/10590737`, with kernel-checked certificates.
Consequently, a nontrivial `T`-cycle with at most two odd runs needs at least `10781274` odd steps
and length at least `17087915`, Eliahou's bound. Larger instances are in `FareyStretch`.

The last section reduces the hypothesis `LinFormHyp` of `LinForm` to the range `k ≥ 10781274`,
since the range `[10^5, 10781274)` is proved here. Results in that section assume
`LinFormHyp 10781274 c μ`, which is not proved here. As in `RunsBridge`, `L` may be any period,
not necessarily minimal, and `oddRuns L x` and `oddSteps L x` count the chosen window.

## Main definitions

- `GapBelow K₁ s`: for all `0 < k < K₁` and `3^k < 2^L`, `2^L ≤ 2^s (2^L − 3^k)`.
- `TwoCircAt k`: the inequality of `TwoCircHyp` at a single `k`.

## Main results

- `farey_bound`, `farey_gap`: for Farey neighbours `p/q > log₂ 3 > p'/q'`, every `0 < k < q + q'`
  with `3^k < 2^L` satisfies `3^k 2^p ≤ 3^q 2^L`, hence `2^L (2^p − 3^q) ≤ 2^p (2^L − 3^k)`.
- `gapBelow_of_farey`: a Farey pair and the check `2^p ≤ 2^s (2^p − 3^q)` give
  `GapBelow (q + q') s`.
- `few_runs_cycle_trivial_of_gap`: under `GapBelow K₁ 30`, a positive `T`-cycle point with at most
  two odd runs and fewer than `K₁` odd steps is `1` or `2`.
- `gapBelow_10781274`: `GapBelow 10781274 30`.
- `few_runs_cycle_trivial_farey`: a positive `T`-cycle point with at most two odd runs and fewer
  than `10781274` odd steps is `1` or `2`.
- `period_ge_of_oddSteps`: a positive `T`-cycle with at least `10781274` odd steps has length at
  least `17087915`.
- `nontrivial_C_cycle_three_runs_farey`: a nontrivial `C`-cycle gives a `T`-cycle point whose
  window has either at least three odd runs, or at least `10781274` odd steps and length at least
  `17087915`.
- `linFormHyp_of_tail`: `LinFormHyp 10781274 c μ` implies `LinFormHyp 100000 c μ` for `c ≥ 30`.

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

/-! ### The Farey-neighbour lemma -/

/-- **Farey-neighbour lemma.** Let `p/q > log₂3 > p'/q'` be Farey
neighbours, in integer form: `p q' = p' q + 1`, `3^q < 2^p`, `2^{p'} < 3^{q'}`.  Then for every
`0 < k < q + q'` and every `L` with `3^k < 2^L` we have `3^k 2^p ≤ 3^q 2^L`, i.e.
`3^k/2^L ≤ 3^q/2^p`: no `3^k/2^L < 1` with `k < q + q'` is closer to `1` than `3^q/2^p`.
The proof writes `k = a q + b q'` and `L = a p + b p'`. -/
theorem farey_bound {p q p' q' k L : ℕ} (hdet : p * q' = p' * q + 1) (hA : 3^q < 2^p)
    (hB : 2^p' < 3^q') (hk0 : 0 < k) (hk : k < q + q') (hL : 3^k < 2^L) :
    3^k * 2^p ≤ 3^q * 2^L := by
  have hZ : (p:ℤ) * q' - p' * q = 1 := by
    have : ((p * q' : ℕ) : ℤ) = ((p' * q + 1 : ℕ) : ℤ) := by rw [hdet]
    push_cast at this; linarith
  set a : ℤ := L * q' - k * p' with ha
  set b : ℤ := p * k - q * L with hb
  have E1 : a * q + b * q' = k := by rw [ha, hb]; linear_combination (k:ℤ) * hZ
  have E2 : a * p + b * p' = L := by rw [ha, hb]; linear_combination (L:ℤ) * hZ
  have hq0 : (0:ℤ) ≤ q := by positivity
  have hq'0 : (0:ℤ) ≤ q' := by positivity
  rcases le_or_gt a 0 with ha0 | ha1 <;> rcases le_or_gt b 0 with hb0 | hb1
  · -- (i)
    exfalso
    have : (k:ℤ) ≤ 0 := by nlinarith
    omega
  · -- (iii) a ≤ 0, b ≥ 1
    exfalso
    obtain ⟨α, hα⟩ : ∃ α : ℕ, a = -(α:ℤ) := ⟨(-a).toNat, by omega⟩
    obtain ⟨β, hβ⟩ : ∃ β : ℕ, b = (β:ℤ) := ⟨b.toNat, by omega⟩
    have hβ1 : β ≠ 0 := by omega
    have N1 : k + α * q = β * q' := by
      have : (k:ℤ) + α * q = β * q' := by rw [hα, hβ] at E1; linarith
      exact_mod_cast this
    have N2 : L + α * p = β * p' := by
      have : (L:ℤ) + α * p = β * p' := by rw [hα, hβ] at E2; linarith
      exact_mod_cast this
    have e1 : 3^k * (3^q)^α = (3^q')^β := by
      rw [← pow_mul, ← pow_mul, ← pow_add, mul_comm q α, mul_comm q' β, N1]
    have e2 : 2^L * (2^p)^α = (2^p')^β := by
      rw [← pow_mul, ← pow_mul, ← pow_add, mul_comm p α, mul_comm p' β, N2]
    have i1 : (2^p')^β < (3^q')^β := Nat.pow_lt_pow_left hB hβ1
    have i2 : (3^q)^α ≤ (2^p)^α := Nat.pow_le_pow_left hA.le α
    have hApos : 0 < (3^q)^α := by positivity
    have : 2^L * (3^q)^α < 3^k * (3^q)^α := by
      calc 2^L * (3^q)^α ≤ 2^L * (2^p)^α := Nat.mul_le_mul_left _ i2
        _ = (2^p')^β := e2
        _ < (3^q')^β := i1
        _ = 3^k * (3^q)^α := e1.symm
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  · -- (iv) a ≥ 1, b ≤ 0
    obtain ⟨γ, hγ⟩ : ∃ γ : ℕ, a = (γ:ℤ) + 1 := ⟨(a-1).toNat, by omega⟩
    obtain ⟨β, hβ⟩ : ∃ β : ℕ, b = -(β:ℤ) := ⟨(-b).toNat, by omega⟩
    have N1 : k + β * q' = (γ+1) * q := by
      have : (k:ℤ) + β * q' = (γ+1) * q := by rw [hγ, hβ] at E1; linarith
      exact_mod_cast this
    have N2 : L + β * p' = (γ+1) * p := by
      have : (L:ℤ) + β * p' = (γ+1) * p := by rw [hγ, hβ] at E2; linarith
      exact_mod_cast this
    have e1 : 3^k * (3^q')^β = 3^q * (3^q)^γ := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, mul_comm q' β, N1]; ring_nf
    have e2 : 2^L * (2^p')^β = 2^p * (2^p)^γ := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, mul_comm p' β, N2]; ring_nf
    have i1 : (3^q)^γ * (2^p')^β ≤ (2^p)^γ * (3^q')^β :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hA.le γ) (Nat.pow_le_pow_left hB.le β)
    have hpos : 0 < (3^q')^β * (2^p')^β := by positivity
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc 3^k * 2^p * ((3^q')^β * (2^p')^β)
        = (3^k * (3^q')^β) * 2^p * (2^p')^β := by ring
      _ = 3^q * 2^p * ((3^q)^γ * (2^p')^β) := by rw [e1]; ring
      _ ≤ 3^q * 2^p * ((2^p)^γ * (3^q')^β) := Nat.mul_le_mul_left _ i1
      _ = 3^q * (2^p * (2^p)^γ) * (3^q')^β := by ring
      _ = 3^q * (2^L * (2^p')^β) * (3^q')^β := by rw [e2]
      _ = 3^q * 2^L * ((3^q')^β * (2^p')^β) := by ring
  · -- (ii)
    exfalso
    have : (k:ℤ) ≥ q + q' := by nlinarith
    omega

/-- Under the hypotheses of `farey_bound`, `2^L (2^p − 3^q) ≤ 2^p (2^L − 3^k)` (both differences
are positive), that is, `1 − 3^k/2^L ≥ 1 − 3^q/2^p`. -/
theorem farey_gap {p q p' q' k L : ℕ} (hdet : p * q' = p' * q + 1) (hA : 3^q < 2^p)
    (hB : 2^p' < 3^q') (hk0 : 0 < k) (hk : k < q + q') (hL : 3^k < 2^L) :
    2^L * (2^p - 3^q) ≤ 2^p * (2^L - 3^k) := by
  have h := farey_bound hdet hA hB hk0 hk hL
  rw [Nat.mul_sub, Nat.mul_sub]
  have : 2^p * 3^k ≤ 2^L * 3^q := by linarith [mul_comm (3^k) (2^p), mul_comm (3^q) (2^L)]
  calc 2^L * 2^p - 2^L * 3^q ≤ 2^L * 2^p - 2^p * 3^k := Nat.sub_le_sub_left this _
    _ = 2^p * 2^L - 2^p * 3^k := by rw [mul_comm (2^L)]

/-! ### Uniform gaps from a Farey pair -/

/-- `GapBelow K1 s`: for all `0 < k < K1` and `L` with `3^k < 2^L`, `2^L ≤ 2^s (2^L − 3^k)`,
that is, `1 − 3^k/2^L ≥ 2^{-s}`. It is proved for concrete `K1` below. -/
def GapBelow (K1 s : ℕ) : Prop :=
  ∀ k L : ℕ, 0 < k → k < K1 → 3^k < 2^L → 2^L ≤ 2^s * (2^L - 3^k)

/-- One Farey pair and one large-number check give `GapBelow (q + q') s`. -/
theorem gapBelow_of_farey {p q p' q' s : ℕ} (hdet : p * q' = p' * q + 1) (hA : 3^q < 2^p)
    (hB : 2^p' < 3^q') (hgap : 2^p ≤ 2^s * (2^p - 3^q)) : GapBelow (q + q') s := by
  intro k L hk0 hk hL
  have G := farey_gap hdet hA hB hk0 hk hL
  have hP : 0 < 2^p := by positivity
  apply Nat.le_of_mul_le_mul_left _ hP
  calc 2^p * 2^L = 2^L * 2^p := mul_comm _ _
    _ ≤ 2^L * (2^s * (2^p - 3^q)) := Nat.mul_le_mul_left _ hgap
    _ = 2^s * (2^L * (2^p - 3^q)) := by ring
    _ ≤ 2^s * (2^p * (2^L - 3^k)) := Nat.mul_le_mul_left _ G
    _ = 2^p * (2^s * (2^L - 3^k)) := by ring

/-- `2^{h+1} ≤ 3^h` for `h ≥ 2`. -/
theorem two_pow_succ_le_three_pow {h : ℕ} (hh : 2 ≤ h) : 2^(h+1) ≤ 3^h := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ, pow_succ 3]; omega

/-! ### Circuits and cycles under a uniform gap -/

/-- `2^30 · 3^50000 ≤ 4^50000` (checked by the kernel). -/
theorem cert_base : 2^30 * 3^50000 ≤ 4^50000 := by decide +kernel

/-- From `GapBelow K1 30`: the `TwoCircHyp` inequality holds for `100000 ≤ k < K1`. -/
theorem twoCirc_of_gap {K1 k L : ℕ} (hG : GapBelow K1 30) (hk : 100000 ≤ k) (hK : k < K1)
    (hL : 3^k < 2^L) : 2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k) := by
  set h := k / 2 with hh
  have h50 : 50000 ≤ h := by omega
  have h2h : 2 * h ≤ k := Nat.mul_div_le k 2
  have s1 : 2^(h+1) + 3^h ≤ 2 * 3^h := by
    have := two_pow_succ_le_three_pow (h := h) (by omega); omega
  have s2 : 2^30 * 3^h ≤ 4^h := by
    obtain ⟨t, ht⟩ : ∃ t, h = 50000 + t := ⟨h - 50000, by omega⟩
    rw [ht, pow_add, pow_add, ← mul_assoc]
    exact Nat.mul_le_mul cert_base (Nat.pow_le_pow_left (by norm_num) t)
  have s3 : 4^h ≤ 2^k := by
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) h2h
  have s4 : 2^30 * (2^(h+1) + 3^h) ≤ 2^(k+1) := by
    calc 2^30 * (2^(h+1) + 3^h) ≤ 2^30 * (2 * 3^h) := Nat.mul_le_mul_left _ s1
      _ = 2 * (2^30 * 3^h) := by ring
      _ ≤ 2 * 2^k := Nat.mul_le_mul_left _ (s2.trans s3)
      _ = 2^(k+1) := by ring
  have G := hG k L (by omega) hK hL
  set S := 2^(h+1) + 3^h
  set D := 2^L - 3^k
  have h30 : 0 < 2^30 := by positivity
  apply Nat.le_of_mul_le_mul_left _ h30
  calc 2^30 * (2^L * S) = 2^L * (2^30 * S) := by ring
    _ ≤ 2^L * 2^(k+1) := Nat.mul_le_mul_left _ s4
    _ ≤ (2^30 * D) * 2^(k+1) := Nat.mul_le_mul_right _ G
    _ = 2^30 * (2^(k+1) * D) := by ring

/-- The `TwoCircHyp` inequality at a single `k`. -/
def TwoCircAt (k : ℕ) : Prop :=
  ∀ L : ℕ, 3^k < 2^L → 2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k)

/-- No 1-circuit with `k` odd steps if the `TwoCircHyp` inequality holds at `k`. -/
theorem one_circuit_false_of_at {m k l : ℕ} (H : TwoCircAt k) (h : IsOneCircuit m k l) :
    False := by
  have s2 := one_circuit_size h
  have s3 := one_circuit_mod_eq_zero h
  have hl := h.2.1
  have hQ : 2 ≤ 2^l := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^l := Nat.pow_le_pow_right (by norm_num) hl
  have hD : 2^(k+l) - 3^k ≤ 2^l - 1 :=
    Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero s3)
  have hH := H (k+l) s2
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

/-- No 2-circuit with `k2 ≤ k1` if the `TwoCircHyp` inequality holds at `k1 + k2`. -/
theorem two_circuit_false_of_at_le {m k1 l1 k2 l2 : ℕ} (H : TwoCircAt (k1 + k2))
    (h : IsTwoCircuit m k1 l1 k2 l2) (hk : k2 ≤ k1) : False := by
  have hsz := two_circuit_size hk h
  have hodd := two_circuit_odd h
  have hL : 0 < k1+l1+k2+l2 := by have := h.1; omega
  have H3 := three_pow_lt_two_pow_of_cycle (by omega) hL h.2.2.2.2.2.2.2.2
  rw [two_circuit_oddSteps h] at H3
  have hH := H (k1+l1+k2+l2) H3
  generalize 2^(k1+l1+k2+l2) = N at *
  generalize 3^(k1+k2) = K at *
  generalize 2^(k1+k2+1) = P at *
  generalize 2^((k1+k2)/2+1) + 3^((k1+k2)/2) = S at *
  obtain ⟨D, rfl⟩ : ∃ D, N = D + K := ⟨N - K, by omega⟩
  rw [Nat.add_sub_cancel] at hH
  nlinarith

/-- No 2-circuit if the `TwoCircHyp` inequality holds at `k1 + k2` (either order). -/
theorem two_circuit_false_of_at {m k1 l1 k2 l2 : ℕ} (H : TwoCircAt (k1 + k2))
    (h : IsTwoCircuit m k1 l1 k2 l2) : False := by
  rcases Nat.le_total k2 k1 with h21 | h12
  · exact two_circuit_false_of_at_le H h h21
  · exact two_circuit_false_of_at_le (by rw [add_comm]; exact H) (two_circuit_rotate h) h12

/-- Under `GapBelow K1 30`, every 1-circuit with `k < K1` odd steps has `m = 1`. -/
theorem one_circuit_eq_one_of_gap {K1 m k l : ℕ} (hG : GapBelow K1 30)
    (h : IsOneCircuit m k l) (hk : k < K1) : m = 1 := by
  rcases Nat.lt_or_ge k 100000 with hk' | hk'
  · exact one_circuit_eq_one h hk'
  · exact (one_circuit_false_of_at (fun _ hL => twoCirc_of_gap hG hk' hk hL) h).elim

/-- Under `GapBelow K1 30`, every 2-circuit with `k1 + k2 < K1` odd steps has `m = 1`. -/
theorem two_circuit_eq_one_of_gap {K1 m k1 l1 k2 l2 : ℕ} (hG : GapBelow K1 30)
    (h : IsTwoCircuit m k1 l1 k2 l2) (hk : k1 + k2 < K1) : m = 1 := by
  rcases Nat.lt_or_ge (k1 + k2) 100000 with hk' | hk'
  · exact two_circuit_eq_one h hk'
  · exact (two_circuit_false_of_at (fun _ hL => twoCirc_of_gap hG hk' hk hL) h).elim

/-- Under `GapBelow K1 30`, a positive `T`-cycle point (at any phase, for any period `L > 0`)
whose window has at most two odd runs and fewer than `K1` odd steps is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_gap {K1 x L : ℕ} (hG : GapBelow K1 30) (hx : 0 < x)
    (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < K1) :
    x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_core hx hL hc hr
    (fun m k l h e =>
      one_circuit_eq_one_of_gap hG h (by rw [one_circuit_oddSteps h] at e; omega))
    (fun m k1 l1 k2 l2 h e =>
      two_circuit_eq_one_of_gap hG h (by rw [two_circuit_oddSteps h] at e; omega))

/-- `2^M < 3^K`, `K ≤ S` and `3^S < 2^L` give `M < L`. Stating this separately keeps large
literals out of `omega`. -/
theorem lt_of_pow_certs {K M S L : ℕ} (hc : 2^M < 3^K) (hS : K ≤ S) (h3 : 3^S < 2^L) :
    M < L := by
  have h4 : 3^K ≤ 3^S := Nat.pow_le_pow_right (by norm_num) hS
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hc.trans_le (h4.trans h3.le))

/-! ### Restricting `LinFormHyp` to large `k` -/

/-- Under `GapBelow K1 s` with `s ≤ c`, the inequality of `LinFormHyp` holds for all
`0 < k < K1`. -/
theorem linFormHyp_range_of_gap {K1 s c μ k L : ℕ} (hG : GapBelow K1 s) (hc : s ≤ c)
    (hk0 : 0 < k) (hk : k < K1) (hL : 3^k < 2^L) : 2^L ≤ 2^c * k^μ * (2^L - 3^k) := by
  have G := hG k L hk0 hk hL
  have h1 : 2^s ≤ 2^c := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : 1 ≤ k^μ := Nat.one_le_pow _ _ hk0
  calc 2^L ≤ 2^s * (2^L - 3^k) := G
    _ ≤ 2^c * 1 * (2^L - 3^k) := by rw [mul_one]; exact Nat.mul_le_mul_right _ h1
    _ ≤ 2^c * k^μ * (2^L - 3^k) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)

/-- Under `GapBelow K1 s` with `s ≤ c`, `LinFormHyp K1 c μ` implies `LinFormHyp 100000 c μ`. -/
theorem linFormHyp_of_tail_gap {K1 s c μ : ℕ} (hG : GapBelow K1 s) (hc : s ≤ c)
    (H : LinFormHyp K1 c μ) : LinFormHyp 100000 c μ := by
  intro k L hk hL
  rcases Nat.lt_or_ge k K1 with hK | hK
  · exact linFormHyp_range_of_gap hG hc (by omega) hK hL
  · exact H k L hK hL

/-- Under `GapBelow K1 30`, `8(c + 17μ + 2) ≤ 2^16` and `LinFormHyp K1 c μ` (which concerns only
`k ≥ K1`), `TwoCircHyp 100000` holds. No condition `c ≥ 30` is needed. -/
theorem twoCircHyp_of_linForm_tail_gap {K1 c μ : ℕ} (hG : GapBelow K1 30)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) : TwoCircHyp 100000 := by
  intro k L hk h3
  rcases Nat.lt_or_ge k K1 with hK | hK
  · exact twoCirc_of_gap hG hk hK h3
  · have hL := H k L hK h3
    have hg := growth (log_cond h0 k (by norm_num; omega))
    set S := 2^(k/2+1) + 3^(k/2)
    set D := 2^L - 3^k
    calc 2^L * S ≤ (2^c * k^μ * D) * S := Nat.mul_le_mul_right _ hL
      _ = (2^c * k^μ * S) * D := by ring
      _ ≤ 2^(k+1) * D := Nat.mul_le_mul_right _ hg.le

/-- Under `GapBelow K1 30`, `8(c + 17μ + 2) ≤ 2^16` and `LinFormHyp K1 c μ`, every 1-circuit
has `m = 1`. -/
theorem one_circuit_eq_one_of_linForm_tail_gap {K1 c μ : ℕ} (hG : GapBelow K1 30)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) {m k l : ℕ}
    (h : IsOneCircuit m k l) : m = 1 :=
  one_circuit_eq_one_of_hyp (twoCircHyp_of_linForm_tail_gap hG h0 H) h

/-- Under `GapBelow K1 30`, `8(c + 17μ + 2) ≤ 2^16` and `LinFormHyp K1 c μ`, every 2-circuit
has `m = 1`. -/
theorem two_circuit_eq_one_of_linForm_tail_gap {K1 c μ : ℕ} (hG : GapBelow K1 30)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) {m k1 l1 k2 l2 : ℕ}
    (h : IsTwoCircuit m k1 l1 k2 l2) : m = 1 :=
  two_circuit_eq_one_of_hyp (twoCircHyp_of_linForm_tail_gap hG h0 H) h

/-- Under `GapBelow K1 30`, `8(c + 17μ + 2) ≤ 2^16` and `LinFormHyp K1 c μ`, every positive
`T`-cycle point with at most two odd runs is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail_gap {K1 c μ : ℕ} (hG : GapBelow K1 30)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) {x L : ℕ} (hx : 0 < x)
    (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_core hx hL hc hr
    (fun _ _ _ h _ => one_circuit_eq_one_of_linForm_tail_gap hG h0 H h)
    (fun _ _ _ _ _ h _ => two_circuit_eq_one_of_linForm_tail_gap hG h0 H h)

/-- Under `GapBelow K1 30` and `2^M < 3^{K1}`, every nontrivial `C`-cycle gives an odd `T`-cycle
point `m ≥ 2^17` whose window either has at least three odd runs, or has at least `K1` odd steps
and length `L > M`. -/
theorem nontrivial_C_cycle_three_runs_of_gap {K1 M : ℕ} (hG : GapBelow K1 30)
    (hM : 2^M < 3^K1) (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
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
    · rcases few_runs_cycle_trivial_of_gap hG (by omega) a4 a5 (by omega) hk with e | e <;>
        omega
    · exact ⟨hk, lt_of_pow_certs hM hk (three_pow_lt_two_pow_of_cycle (by omega) a4 a5)⟩
  · exact Or.inr hr

/-- Under `GapBelow K1 30`, `8(c + 17μ + 2) ≤ 2^16` and `LinFormHyp K1 c μ`, every nontrivial
`C`-cycle gives an odd `T`-cycle point `m ≥ 2^17` whose window has at least three odd runs. -/
theorem nontrivial_C_cycle_three_runs_of_linForm_tail_gap {K1 c μ : ℕ} (hG : GapBelow K1 30)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 3 ≤ oddRuns L m := by
  obtain ⟨m, L, a1, a2, a3, a4, a5, -, -⟩ := nontrivial_C_cycle_runs n hn ℓ hℓ h h1 h2 h4
  refine ⟨m, L, a1, a2, a3, a4, a5, ?_⟩
  have : (2:ℕ)^17 = 131072 := by norm_num
  by_contra hh
  rcases few_runs_cycle_trivial_of_linForm_tail_gap hG h0 H (by omega) a4 a5 (by omega) with
    e | e <;> omega

/-! ### The instance `K₁ = 10781274` -/

/-- Determinant of the Farey pair `301994/190537 > log₂3 > 16785921/10590737`. -/
theorem cert_det : 301994 * 10590737 = 16785921 * 190537 + 1 := by norm_num

/-- `3^190537 < 2^301994` (checked by the kernel). -/
theorem cert_above : 3^190537 < 2^301994 := by decide +kernel

/-- `2^301994 ≤ 2^30 (2^301994 − 3^190537)` (checked by the kernel). -/
theorem cert_gap : 2^301994 ≤ 2^30 * (2^301994 - 3^190537) := by decide +kernel

theorem cert_below_split : 2^8392960 * 2^8392961 < 3^10590737 := by decide +kernel

/-- `2^16785921 < 3^10590737` (checked by the kernel, with the exponent split below `2^24`). -/
theorem cert_below : 2^16785921 < 3^10590737 := by
  rw [show 16785921 = 8392960 + 8392961 from rfl, pow_add]; exact cert_below_split

/-- `GapBelow 10781274 30`. -/
theorem gapBelow_10781274 : GapBelow 10781274 30 :=
  gapBelow_of_farey cert_det cert_above cert_below cert_gap

/-- For `0 < k < 10781274` and `3^k < 2^L`: `2^L ≤ 2^30 (2^L − 3^k)`. -/
theorem gap_farey {k L : ℕ} (hk0 : 0 < k) (hk : k < 10781274) (hL : 3^k < 2^L) :
    2^L ≤ 2^30 * (2^L - 3^k) := gapBelow_10781274 k L hk0 hk hL

/-- The inequality of `TwoCircHyp` holds on `[10^5, 10781274)`. -/
theorem twoCirc_range {k L : ℕ} (hk : 100000 ≤ k) (hK : k < 10781274) (hL : 3^k < 2^L) :
    2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k) :=
  twoCirc_of_gap gapBelow_10781274 hk hK hL

/-- Every 1-circuit with `k < 10781274` odd steps has `m = 1`. -/
theorem one_circuit_eq_one_farey {m k l : ℕ} (h : IsOneCircuit m k l) (hk : k < 10781274) :
    m = 1 := one_circuit_eq_one_of_gap gapBelow_10781274 h hk

/-- Every 2-circuit with `k1 + k2 < 10781274` odd steps has `m = 1`. -/
theorem two_circuit_eq_one_farey {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2)
    (hk : k1 + k2 < 10781274) : m = 1 := two_circuit_eq_one_of_gap gapBelow_10781274 h hk

/-- A positive `T`-cycle point `x` (at any phase, for any period `L > 0`, not necessarily
minimal) whose window has at most two odd runs and fewer than `10781274` odd steps is `1` or
`2`. -/
theorem few_runs_cycle_trivial_farey {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < 10781274) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_gap gapBelow_10781274 hx hL hc hr hk

theorem cert_eliahou_split : 2^8543957 * 2^8543957 < 3^5390637 * 3^5390637 := by
  decide +kernel

/-- `2^17087914 < 3^10781274` (checked by the kernel). -/
theorem cert_eliahou : 2^17087914 < 3^10781274 := by
  rw [show 17087914 = 8543957 + 8543957 from rfl, show 10781274 = 5390637 + 5390637 from rfl,
    pow_add, pow_add]; exact cert_eliahou_split

/-- **Eliahou's bound.** If a positive `T`-cycle of length `L` has at least `10781274` odd steps,
then `L ≥ 17087915`. -/
theorem period_ge_of_oddSteps {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (hc : T^[L] m = m)
    (hk : 10781274 ≤ oddSteps L m) : 17087915 ≤ L :=
  lt_of_pow_certs cert_eliahou hk (three_pow_lt_two_pow_of_cycle hm hL hc)

/-- A nontrivial positive `C`-cycle point `n` yields an odd `T`-cycle point `m` with
`2^17 ≤ m ≤ n` and period `L > 0` such that `oddSteps L m ≥ 971`; either `oddSteps L m ≥ 10^4` or
there are at least `54` odd runs; and either `oddSteps L m ≥ 10781274` and `L ≥ 17087915`, or
there are at least three odd runs. -/
theorem nontrivial_C_cycle_three_runs_farey (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) ∧
      ((10781274 ≤ oddSteps L m ∧ 17087915 ≤ L) ∨ 3 ≤ oddRuns L m) :=
  nontrivial_C_cycle_three_runs_of_gap gapBelow_10781274 cert_eliahou n hn ℓ hℓ h h1 h2 h4

/-! ### `LinFormHyp` for `k ≥ 10781274` suffices -/

/-- For `c ≥ 30` and any `μ`, the inequality of `LinFormHyp`
`2^L ≤ 2^c k^μ (2^L − 3^k)` holds for all `0 < k < 10781274` with `3^k < 2^L`. -/
theorem linFormHyp_range {c μ k L : ℕ} (hc : 30 ≤ c) (hk0 : 0 < k) (hk : k < 10781274)
    (hL : 3^k < 2^L) : 2^L ≤ 2^c * k^μ * (2^L - 3^k) :=
  linFormHyp_range_of_gap gapBelow_10781274 hc hk0 hk hL

/-- For `c ≥ 30`, `LinFormHyp 10781274 c μ` implies `LinFormHyp 100000 c μ`. -/
theorem linFormHyp_of_tail {c μ : ℕ} (hc : 30 ≤ c) (H : LinFormHyp 10781274 c μ) :
    LinFormHyp 100000 c μ := linFormHyp_of_tail_gap gapBelow_10781274 hc H

/-- Under `LinFormHyp 10781274 c μ` and `8(c + 17μ + 2) ≤ 2^16`, `TwoCircHyp 100000` holds. -/
theorem twoCircHyp_of_linForm_tail {c μ : ℕ} (h0 : 8 * (c + 17*μ + 2) ≤ 2^16)
    (H : LinFormHyp 10781274 c μ) : TwoCircHyp 100000 :=
  twoCircHyp_of_linForm_tail_gap gapBelow_10781274 h0 H

/-- Under `LinFormHyp 10781274 c μ` and `8(c + 17μ + 2) ≤ 2^16`, every 1-circuit has `m = 1`. -/
theorem one_circuit_eq_one_of_linForm_tail {c μ : ℕ} (h0 : 8 * (c + 17*μ + 2) ≤ 2^16)
    (H : LinFormHyp 10781274 c μ) {m k l : ℕ} (h : IsOneCircuit m k l) : m = 1 :=
  one_circuit_eq_one_of_linForm_tail_gap gapBelow_10781274 h0 H h

/-- Under `LinFormHyp 10781274 c μ` and `8(c + 17μ + 2) ≤ 2^16`, every 2-circuit has `m = 1`. -/
theorem two_circuit_eq_one_of_linForm_tail {c μ : ℕ} (h0 : 8 * (c + 17*μ + 2) ≤ 2^16)
    (H : LinFormHyp 10781274 c μ) {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) :
    m = 1 :=
  two_circuit_eq_one_of_linForm_tail_gap gapBelow_10781274 h0 H h

/-- Under `LinFormHyp 10781274 100 14`, an irrationality-measure bound for `k ≥ 10781274` only,
every positive `T`-cycle point (at any phase, for any period) with at most two odd runs is `1` or
`2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail (H : LinFormHyp 10781274 100 14) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm_tail_gap gapBelow_10781274 (by norm_num) H hx hL hc hr

/-- Under `LinFormHyp 10781274 100 14`, every nontrivial `C`-cycle yields a `T`-cycle point
`m ≥ 2^17` whose window has at least three odd runs. -/
theorem nontrivial_C_cycle_three_runs_of_linForm_tail (H : LinFormHyp 10781274 100 14)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 3 ≤ oddRuns L m :=
  nontrivial_C_cycle_three_runs_of_linForm_tail_gap gapBelow_10781274 (by norm_num) H
    n hn ℓ hℓ h h1 h2 h4

/-! ### Examples -/

-- The Farey-neighbour lemma for the pair `485/306 > log₂ 3 > 1054/665`, at `k = 5`, `L = 8`.
example : 3^5 * 2^485 ≤ 3^306 * 2^8 :=
  farey_bound (p := 485) (q := 306) (p' := 1054) (q' := 665) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

-- The trivial cycle satisfies the hypotheses of `few_runs_cycle_trivial_farey`.
example : 0 < 1 ∧ 0 < 2 ∧ T^[2] 1 = 1 ∧ oddRuns 2 1 ≤ 2 ∧ oddSteps 2 1 < 10781274 := by decide

-- `GapBelow 6 1` fails: at `k = 5`, `L = 8`, `2^8 = 256 > 2 · (256 − 243) = 26`.
example : ¬ GapBelow 6 1 := by
  intro h
  have := h 5 8 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

-- `GapBelow 6 0` fails, with the same witness.
example : ¬ GapBelow 6 0 := by
  intro h
  have := h 5 8 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

end Collatz
