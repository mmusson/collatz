import RunsBridge
import Mathlib.Tactic

/-!
# Farey-neighbour (two-convergent) reduction for `2^L − 3^k`

* **T1** `farey_bound`, `farey_gap`: for Farey neighbours `p/q > log₂3 > p'/q'`
  (`p q' = p' q + 1`), every `0 < k < q+q'` with `3^k < 2^L` satisfies
  `3^k 2^p ≤ 3^q 2^L`, hence `2^L (2^p−3^q) ≤ 2^p (2^L−3^k)`.  Pure integer proof.
* `GapBelow K1 s` (a **proved** property for concrete `K1`): `2^L ≤ 2^s (2^L−3^k)` for all
  `0 < k < K1`, `3^k < 2^L`.  `gapBelow_of_farey`: one Farey pair plus one bignum check
  `2^p ≤ 2^s (2^p − 3^q)` gives `GapBelow (q+q') s`.
* Generic consequences of `GapBelow K1 30`: the `TwoCircHyp` inequality on `[10^5, K1)`
  (`twoCirc_of_gap`), 1- and 2-circuit exclusion for `k < K1`, few-run cycle exclusion for
  `S_L < K1`, and `LinFormHyp K1 c μ ⇒ LinFormHyp 10^5 c μ` / `⇒ TwoCircHyp 10^5`.
* **T2** instance `K1 = 10781274` (pair `(q,p) = (190537, 301994)`,
  `(q',p') = (10590737, 16785921)`, kernel certificates via `decide +kernel`, exponents above
  `2^24` split with `pow_add`): **unconditionally**, no nontrivial `T`-cycle (any phase, any
  period `L`) has `≤ 2` odd runs and `S_L < 10781274` (`few_runs_cycle_trivial_farey`), and
  such a cycle with `≤ 2` runs would need `L ≥ 17087915` (`period_ge_of_oddSteps`).
  Larger instances (`K1 = 64497107`, `K1 = 225644606`) are in `FareyStretch.lean`.
* **T3** (`*_of_linForm_tail`): still **CONDITIONAL** on the unformalized `LinFormHyp`, but now
  only for `k ≥ 10781274`; the range `[10^5, 10781274)` of that hypothesis is a theorem here
  (`linFormHyp_range`).  The literature (Rhin 1987; Wu–Wang) makes the tail plausible [`IrrMeasureReal`: Wu–Wang 2014, J. Number Theory, DOI 10.1016/j.jnt.2014.03.007, 'On the irrationality measure of log 3', concerns log 3, NOT log 3/log 2], but its
  explicit constants `(c, μ) = (100, 14)` are still unchecked.

About `L`: as in `RunsBridge`, `L` may be any period (not necessarily minimal); `oddRuns L x`,
`oddSteps L x` then count the chosen window (`t` laps give `t` times the per-lap values).

This is the classical continued-fraction reduction (Eliahou 1993; Simons–de Weger).
The unconditional results are finite instances of Steiner (1977) / Simons (2005).
-/

namespace Collatz
open CollatzProof

/-- **T1 (two-convergent / Farey-neighbour lemma).**  Let `p/q > log₂3 > p'/q'` be Farey
neighbours, in integer form: `p q' = p' q + 1`, `3^q < 2^p`, `2^{p'} < 3^{q'}`.  Then for every
`0 < k < q + q'` and every `L` with `3^k < 2^L` we have `3^k 2^p ≤ 3^q 2^L`, i.e.
`3^k/2^L ≤ 3^q/2^p`: no `3^k/2^L < 1` with `k < q+q'` is closer to `1` than `3^q/2^p`.
Pure `ℕ/ℤ` proof (no reals, no logarithms), via `k = a q + b q'`, `L = a p + b p'`. -/
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

/-- **T1 corollary.** Same hypotheses: `2^L (2^p − 3^q) ≤ 2^p (2^L − 3^k)` (ℕ subtraction,
both differences positive), i.e. `1 − 3^k/2^L ≥ 1 − 3^q/2^p`. -/
theorem farey_gap {p q p' q' k L : ℕ} (hdet : p * q' = p' * q + 1) (hA : 3^q < 2^p)
    (hB : 2^p' < 3^q') (hk0 : 0 < k) (hk : k < q + q') (hL : 3^k < 2^L) :
    2^L * (2^p - 3^q) ≤ 2^p * (2^L - 3^k) := by
  have h := farey_bound hdet hA hB hk0 hk hL
  rw [Nat.mul_sub, Nat.mul_sub]
  have : 2^p * 3^k ≤ 2^L * 3^q := by linarith [mul_comm (3^k) (2^p), mul_comm (3^q) (2^L)]
  calc 2^L * 2^p - 2^L * 3^q ≤ 2^L * 2^p - 2^p * 3^k := Nat.sub_le_sub_left this _
    _ = 2^p * 2^L - 2^p * 3^k := by rw [mul_comm (2^L)]


/-! ## Generic machinery: `GapBelow K1 s` -/

/-- `GapBelow K1 s`: for all `0 < k < K1` and `L` with `3^k < 2^L`, `2^L ≤ 2^s (2^L − 3^k)`,
i.e. `1 − 3^k/2^L ≥ 2^{-s}`.  This is proved (not assumed) for concrete `K1` below. -/
def GapBelow (K1 s : ℕ) : Prop :=
  ∀ k L : ℕ, 0 < k → k < K1 → 3^k < 2^L → 2^L ≤ 2^s * (2^L - 3^k)

/-- One Farey pair and one bignum check give `GapBelow (q+q') s`. -/
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

/-- Kernel certificate: `2^30 · 3^50000 ≤ 4^50000`. -/
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
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) h2h
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
  obtain ⟨-, s2, s3⟩ := one_circuit_size h
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

/-- `GapBelow K1 30` ⇒ every 1-circuit with `k < K1` odd steps has `m = 1`. -/
theorem one_circuit_eq_one_of_gap {K1 m k l : ℕ} (hG : GapBelow K1 30)
    (h : IsOneCircuit m k l) (hk : k < K1) : m = 1 := by
  rcases Nat.lt_or_ge k 100000 with hk' | hk'
  · exact one_circuit_eq_one h hk'
  · exact (one_circuit_false_of_at (fun _ hL => twoCirc_of_gap hG hk' hk hL) h).elim

/-- `GapBelow K1 30` ⇒ every 2-circuit with `k1 + k2 < K1` odd steps has `m = 1`. -/
theorem two_circuit_eq_one_of_gap {K1 m k1 l1 k2 l2 : ℕ} (hG : GapBelow K1 30)
    (h : IsTwoCircuit m k1 l1 k2 l2) (hk : k1 + k2 < K1) : m = 1 := by
  rcases Nat.lt_or_ge (k1 + k2) 100000 with hk' | hk'
  · exact two_circuit_eq_one h hk'
  · exact (two_circuit_false_of_at (fun _ hL => twoCirc_of_gap hG hk' hk hL) h).elim

/-- `GapBelow K1 30` ⇒ a positive `T`-cycle point (any phase, any period `L > 0`) whose window
has `≤ 2` odd runs and `S_L(x) < K1` odd steps is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_gap {K1 x L : ℕ} (hG : GapBelow K1 30) (hx : 0 < x)
    (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < K1) :
    x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_core hx hL hc hr
    (fun m k l h e => one_circuit_eq_one_of_gap hG h (by rw [one_circuit_oddSteps h] at e; omega))
    (fun m k1 l1 k2 l2 h e =>
      two_circuit_eq_one_of_gap hG h (by rw [two_circuit_oddSteps h] at e; omega))

/-- Generic transfer: `2^M < 3^K`, `K ≤ S` and `3^S < 2^L` give `M < L`. (Keeps big
literals out of `omega`, which would try to evaluate them.) -/
theorem lt_of_pow_certs {K M S L : ℕ} (hc : 2^M < 3^K) (hS : K ≤ S) (h3 : 3^S < 2^L) :
    M < L := by
  have h4 : 3^K ≤ 3^S := Nat.pow_le_pow_right (by norm_num) hS
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hc.trans_le (h4.trans h3.le))

/-- `GapBelow K1 s`, `s ≤ c`: the `LinFormHyp` inequality holds for all `0 < k < K1`. -/
theorem linFormHyp_range_of_gap {K1 s c μ k L : ℕ} (hG : GapBelow K1 s) (hc : s ≤ c)
    (hk0 : 0 < k) (hk : k < K1) (hL : 3^k < 2^L) : 2^L ≤ 2^c * k^μ * (2^L - 3^k) := by
  have G := hG k L hk0 hk hL
  have h1 : 2^s ≤ 2^c := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : 1 ≤ k^μ := Nat.one_le_pow _ _ hk0
  calc 2^L ≤ 2^s * (2^L - 3^k) := G
    _ ≤ 2^c * 1 * (2^L - 3^k) := by rw [mul_one]; exact Nat.mul_le_mul_right _ h1
    _ ≤ 2^c * k^μ * (2^L - 3^k) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)

/-- `GapBelow K1 s`, `s ≤ c`: `LinFormHyp K1 c μ ⇒ LinFormHyp 100000 c μ`. -/
theorem linFormHyp_of_tail_gap {K1 s c μ : ℕ} (hG : GapBelow K1 s) (hc : s ≤ c)
    (H : LinFormHyp K1 c μ) : LinFormHyp 100000 c μ := by
  intro k L hk hL
  rcases Nat.lt_or_ge k K1 with hK | hK
  · exact linFormHyp_range_of_gap hG hc (by omega) hK hL
  · exact H k L hK hL

/-- CONDITIONAL (on `LinFormHyp K1 c μ`, i.e. only for `k ≥ K1`): with `GapBelow K1 30` and
`8(c+17μ+2) ≤ 2^16`, `TwoCircHyp 100000` holds.  No condition `c ≥ 30` is needed. -/
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

/-- CONDITIONAL (on `LinFormHyp K1 c μ`): no nontrivial 1- or 2-circuits. -/
theorem no_circuits_of_linForm_tail_gap {K1 c μ : ℕ} (hG : GapBelow K1 30)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) :
    (∀ m k l, IsOneCircuit m k l → m = 1) ∧
      (∀ m k1 l1 k2 l2, IsTwoCircuit m k1 l1 k2 l2 → m = 1) :=
  have H' := twoCircHyp_of_linForm_tail_gap hG h0 H
  ⟨fun _ _ _ h => one_circuit_eq_one_of_hyp H' h,
   fun _ _ _ _ _ h => two_circuit_eq_one_of_hyp H' h⟩

/-- CONDITIONAL (on `LinFormHyp K1 c μ`): every positive `T`-cycle point with `≤ 2` odd runs
is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail_gap {K1 c μ : ℕ} (hG : GapBelow K1 30)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K1 c μ) {x L : ℕ} (hx : 0 < x)
    (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  have HH := no_circuits_of_linForm_tail_gap hG h0 H
  few_runs_cycle_trivial_core hx hL hc hr (fun m k l h _ => HH.1 m k l h)
    (fun m k1 l1 k2 l2 h _ => HH.2 m k1 l1 k2 l2 h)

/-- Generic corollary for `C`-cycles: `GapBelow K1 30` and `2^M < 3^{K1}` ⇒ every nontrivial
`C`-cycle gives an odd `T`-cycle point `m ≥ 2^17` whose window either has `≥ 3` odd runs or
has `S_L(m) ≥ K1` and `L > M`. -/
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
    · rcases few_runs_cycle_trivial_of_gap hG (by omega) a4 a5 (by omega) hk with e | e <;> omega
    · exact ⟨hk, lt_of_pow_certs hM hk (three_pow_lt_two_pow_of_cycle (by omega) a4 a5)⟩
  · exact Or.inr hr

/-- Generic corollary for `C`-cycles, CONDITIONAL on `LinFormHyp K1 c μ`. -/
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

/-! ## T2: the instance `K1 = 10781274` -/

/-- Determinant of the Farey pair `301994/190537 > log₂3 > 16785921/10590737`. -/
theorem cert_det : 301994 * 10590737 = 16785921 * 190537 + 1 := by norm_num
/-- `3^190537 < 2^301994` (kernel certificate). -/
theorem cert_above : 3^190537 < 2^301994 := by decide +kernel
/-- `2^301994 ≤ 2^30 (2^301994 − 3^190537)` (kernel certificate). -/
theorem cert_gap : 2^301994 ≤ 2^30 * (2^301994 - 3^190537) := by decide +kernel
theorem cert_below_split : 2^8392960 * 2^8392961 < 3^10590737 := by decide +kernel
/-- `2^16785921 < 3^10590737` (kernel certificate, exponent split below `2^24`). -/
theorem cert_below : 2^16785921 < 3^10590737 := by
  rw [show 16785921 = 8392960 + 8392961 from rfl, pow_add]; exact cert_below_split

/-- **Proved:** `GapBelow 10781274 30`. -/
theorem gapBelow_10781274 : GapBelow 10781274 30 :=
  gapBelow_of_farey cert_det cert_above cert_below cert_gap

/-- **T2(a).** For `0 < k < 10781274` and `3^k < 2^L`: `2^L ≤ 2^30 (2^L − 3^k)`. -/
theorem gap_farey {k L : ℕ} (hk0 : 0 < k) (hk : k < 10781274) (hL : 3^k < 2^L) :
    2^L ≤ 2^30 * (2^L - 3^k) := gapBelow_10781274 k L hk0 hk hL

/-- **T2(b).** The `TwoCircHyp` inequality holds unconditionally on `[10^5, 10781274)`. -/
theorem twoCirc_range {k L : ℕ} (hk : 100000 ≤ k) (hK : k < 10781274) (hL : 3^k < 2^L) :
    2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k) :=
  twoCirc_of_gap gapBelow_10781274 hk hK hL

/-- **T2(c).** Every 1-circuit with `k < 10781274` odd steps has `m = 1`. -/
theorem one_circuit_eq_one_farey {m k l : ℕ} (h : IsOneCircuit m k l) (hk : k < 10781274) :
    m = 1 := one_circuit_eq_one_of_gap gapBelow_10781274 h hk

/-- **T2(c).** Every 2-circuit with `k1 + k2 < 10781274` odd steps has `m = 1`. -/
theorem two_circuit_eq_one_farey {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2)
    (hk : k1 + k2 < 10781274) : m = 1 := two_circuit_eq_one_of_gap gapBelow_10781274 h hk

/-- **T2(c), unconditional, rotation-free.** A positive `T`-cycle point `x` (any phase; `L` any
period `> 0`, not necessarily minimal) whose window has `≤ 2` odd runs and `S_L(x) < 10781274`
odd steps is `1` or `2`.  (Finite instance of Steiner 1977 / Simons 2005.) -/
theorem few_runs_cycle_trivial_farey {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < 10781274) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_gap gapBelow_10781274 hx hL hc hr hk

theorem cert_eliahou_split : 2^8543957 * 2^8543957 < 3^5390637 * 3^5390637 := by
  decide +kernel
/-- `2^17087914 < 3^10781274` (kernel certificate). -/
theorem cert_eliahou : 2^17087914 < 3^10781274 := by
  rw [show 17087914 = 8543957 + 8543957 from rfl, show 10781274 = 5390637 + 5390637 from rfl,
    pow_add, pow_add]; exact cert_eliahou_split

/-- If `S_L(m) ≥ 10781274` on a positive `T`-cycle of length `L`, then `L ≥ 17087915`
(Eliahou's number). -/
theorem period_ge_of_oddSteps {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (hc : T^[L] m = m)
    (hk : 10781274 ≤ oddSteps L m) : 17087915 ≤ L :=
  lt_of_pow_certs cert_eliahou hk (three_pow_lt_two_pow_of_cycle hm hL hc)

/-- **T2(c), for `C`-cycles, unconditional.** A nontrivial positive `C`-cycle point `n` yields an
odd `T`-cycle point `m`, `2^17 ≤ m ≤ n`, period `L > 0`, `S_L(m) ≥ 971`,
(`S_L(m) ≥ 10^4` or `≥ 54` runs), and (`S_L(m) ≥ 10781274` and `L ≥ 17087915`, or `≥ 3` runs). -/
theorem nontrivial_C_cycle_three_runs_farey (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) ∧
      ((10781274 ≤ oddSteps L m ∧ 17087915 ≤ L) ∨ 3 ≤ oddRuns L m) :=
  nontrivial_C_cycle_three_runs_of_gap gapBelow_10781274 cert_eliahou n hn ℓ hℓ h h1 h2 h4

/-! ## T3: `LinFormHyp` only matters for `k ≥ 10781274` -/

/-- **T3(a), unconditional.** For `c ≥ 30`, any `μ`: the `LinFormHyp` inequality
`2^L ≤ 2^c k^μ (2^L − 3^k)` holds for all `0 < k < 10781274` with `3^k < 2^L`. -/
theorem linFormHyp_range {c μ k L : ℕ} (hc : 30 ≤ c) (hk0 : 0 < k) (hk : k < 10781274)
    (hL : 3^k < 2^L) : 2^L ≤ 2^c * k^μ * (2^L - 3^k) :=
  linFormHyp_range_of_gap gapBelow_10781274 hc hk0 hk hL

/-- **T3(b).** `LinFormHyp 10781274 c μ ⇒ LinFormHyp 100000 c μ` (for `c ≥ 30`). -/
theorem linFormHyp_of_tail {c μ : ℕ} (hc : 30 ≤ c) (H : LinFormHyp 10781274 c μ) :
    LinFormHyp 100000 c μ := linFormHyp_of_tail_gap gapBelow_10781274 hc H

/-- **T3(c), CONDITIONAL** on the unformalized `LinFormHyp 10781274 c μ`:
`8(c+17μ+2) ≤ 2^16` ⇒ `TwoCircHyp 100000`. -/
theorem twoCircHyp_of_linForm_tail {c μ : ℕ} (h0 : 8 * (c + 17*μ + 2) ≤ 2^16)
    (H : LinFormHyp 10781274 c μ) : TwoCircHyp 100000 :=
  twoCircHyp_of_linForm_tail_gap gapBelow_10781274 h0 H

/-- **T3(d), CONDITIONAL** on the unformalized `LinFormHyp 10781274 c μ`: no nontrivial 1- or
2-circuits. -/
theorem no_circuits_of_linForm_tail {c μ : ℕ} (h0 : 8 * (c + 17*μ + 2) ≤ 2^16)
    (H : LinFormHyp 10781274 c μ) :
    (∀ m k l, IsOneCircuit m k l → m = 1) ∧
      (∀ m k1 l1 k2 l2, IsTwoCircuit m k1 l1 k2 l2 → m = 1) :=
  no_circuits_of_linForm_tail_gap gapBelow_10781274 h0 H

/-- **T3(d), CONDITIONAL** on `LinFormHyp 10781274 100 14` (i.e. on an irrationality-measure
bound only for `k ≥ 10781274`; the range `[10^5, 10781274)` is proved; the constants have not
been checked against Rhin 1987 / Wu–Wang): every positive `T`-cycle point with `≤ 2` odd runs
(any phase, any period) is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail (H : LinFormHyp 10781274 100 14) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm_tail_gap gapBelow_10781274 (by norm_num) H hx hL hc hr

/-- **T3(d), for `C`-cycles, CONDITIONAL** on `LinFormHyp 10781274 100 14`: every nontrivial
`C`-cycle yields a `T`-cycle point `m ≥ 2^17` whose window has at least 3 odd runs. -/
theorem nontrivial_C_cycle_three_runs_of_linForm_tail (H : LinFormHyp 10781274 100 14)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 3 ≤ oddRuns L m :=
  nontrivial_C_cycle_three_runs_of_linForm_tail_gap gapBelow_10781274 (by norm_num) H
    n hn ℓ hℓ h h1 h2 h4

/-! ## Sanity checks -/

/-- Small instance of T1: `485/306 > log₂3 > 1054/665` are Farey neighbours; `k = 5, L = 8`. -/
example : 3^5 * 2^485 ≤ 3^306 * 2^8 :=
  farey_bound (p := 485) (q := 306) (p' := 1054) (q' := 665) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuity: the hypotheses of `few_runs_cycle_trivial_farey` are met by the trivial cycle
(the only known instance). -/
example : 0 < 1 ∧ 0 < 2 ∧ T^[2] 1 = 1 ∧ oddRuns 2 1 ≤ 2 ∧ oddSteps 2 1 < 10781274 := by decide

/-- Discrimination check: `GapBelow` is not vacuous.  At `k = 5`, `L = 8`:
`3^5 = 243 < 256 = 2^8` but `2^8 = 256 > 2·(256 − 243) = 26`, so `GapBelow 6 1` fails. -/
example : ¬ GapBelow 6 1 := by
  intro h
  have := h 5 8 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- Also `¬ GapBelow 6 0` (same witness). -/
example : ¬ GapBelow 6 0 := by
  intro h
  have := h 5 8 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

end Collatz

#print axioms Collatz.farey_bound
#print axioms Collatz.farey_gap
#print axioms Collatz.gapBelow_of_farey
#print axioms Collatz.twoCirc_of_gap
#print axioms Collatz.one_circuit_eq_one_of_gap
#print axioms Collatz.two_circuit_eq_one_of_gap
#print axioms Collatz.few_runs_cycle_trivial_of_gap
#print axioms Collatz.linFormHyp_of_tail_gap
#print axioms Collatz.twoCircHyp_of_linForm_tail_gap
#print axioms Collatz.few_runs_cycle_trivial_of_linForm_tail_gap
#print axioms Collatz.nontrivial_C_cycle_three_runs_of_gap
#print axioms Collatz.nontrivial_C_cycle_three_runs_of_linForm_tail_gap
#print axioms Collatz.gapBelow_10781274
#print axioms Collatz.gap_farey
#print axioms Collatz.twoCirc_range
#print axioms Collatz.one_circuit_eq_one_farey
#print axioms Collatz.two_circuit_eq_one_farey
#print axioms Collatz.few_runs_cycle_trivial_farey
#print axioms Collatz.period_ge_of_oddSteps
#print axioms Collatz.nontrivial_C_cycle_three_runs_farey
#print axioms Collatz.linFormHyp_range
#print axioms Collatz.linFormHyp_of_tail
#print axioms Collatz.twoCircHyp_of_linForm_tail
#print axioms Collatz.no_circuits_of_linForm_tail
#print axioms Collatz.few_runs_cycle_trivial_of_linForm_tail
#print axioms Collatz.nontrivial_C_cycle_three_runs_of_linForm_tail
