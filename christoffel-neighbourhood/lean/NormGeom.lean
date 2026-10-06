import NormMixedRev

/-!
# cycle geometry and the vacuity of `cycle_mixed_flips_rev`

* `cycle_ratio`: every nontrivial positive `T`-cycle (odd point `m ≠ 1`, period `L`, `r` odd
  steps) satisfies `2^L · M^r ≤ (3M+1)^r` with `M = 293601280` (the Crandall sandwich at the
  cycle minimum `x ≥ M`, `cycleMinAbove_29`, and monotonicity of `(3x+1)/x`), hence
  `200 L < 317 r` (`(3M+1)^200 < 2^317 M^200`, a kernel `decide` on ~1700-digit naturals).
  `cycle_params'` packages `L < 2r`, `r ≥ 40901`, `200L < 317r`.
* `up_site_of_valid_mixed`, `down_site_of_valid_mixed`: in a valid word whose partial sums are
  those of `chr r A` plus one at `k` and minus one at `k'`, `k` is an up-site
  (`ρ ≥ r - a`) and `k'` a down-site (`ρ' < a`), `a = A mod r = A - r`.
* `cycle_mixed_flips_rev_vacuous`: the hypotheses of `NormBig`'s
  `NormMixedRev.cycle_mixed_flips_rev` (even without coprimality) are contradictory: that
  theorem is **cycle-vacuous**. Elementary proof, no norm engine.

Infrastructure only. The window `200L < 317r`
(i.e. `L/r < 1.585`) is a routine consequence of the published cycle-minimum bound, just above
`log₂ 3 ≈ 1.58496`.
-/

namespace Collatz.NormGeom
open Collatz.NormGoal Collatz.NormBridge CollatzProof Finset Collatz.NormCycleAll

set_option exponentiation.threshold 400 in
/-- `(3M+1)^200 < 2^317 M^200` for `M = 293601280`. -/
theorem num_step : (880803841:ℕ) ^ 200 < 2 ^ 317 * 293601280 ^ 200 := by decide

/-- **Cycle ratio.** For a nontrivial positive `T`-cycle through an odd point
`m ≠ 1` with `r` odd steps in period `L`: `2^L · 293601280^r ≤ 880803841^r` and `200L < 317r`. -/
theorem cycle_ratio {m L r : ℕ} {v : ℕ → ℕ} (hr : 1 ≤ r) (hv1 : ∀ i < r, 1 ≤ v i)
    (hL : psum v r = L) (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j))
    (hcyc : T^[L] m = m) (hm : m ≠ 1) :
    2 ^ L * 293601280 ^ r ≤ 880803841 ^ r ∧ 200 * L < 317 * r := by
  have hS : oddSteps L m = r := by
    have := oddSteps_psum hv1 hL hodd r le_rfl; rwa [hL] at this
  have hLr : r ≤ L := by
    have : ∀ i ≤ r, i ≤ psum v i := by
      intro i
      induction i with
      | zero => intro _; simp [psum]
      | succ i ih =>
        intro hi; rw [psum_succ]; have := ih (by omega); have := hv1 i (by omega); omega
    have := this r le_rfl; omega
  have hL0 : 0 < L := by omega
  have hmodd : m % 2 = 1 := by
    have := (hodd 0 hL0).mpr ⟨0, by omega, by simp [psum]⟩
    simpa using this
  have hm0 : 0 < m := by omega
  obtain ⟨a, ha, hmin, hxper⟩ := exists_cycle_min hL0 hcyc
  obtain ⟨b, _, hmax⟩ := exists_orbit_max T hL0 hcyc
  have hm0a : 0 < T^[a] m := iterate_T_pos hm0 a
  have hsand := (cycle_sandwich (b := b) hcyc hm0a hmin (fun i => by
    rw [← Function.iterate_add_apply]; exact hmax _)).1
  rw [hS] at hsand
  set x := T^[a] m with hx
  have hx1 : x ≠ 1 := by
    intro e
    have hxM : T^[L - a] x = m := by
      rw [hx, ← Function.iterate_add_apply, Nat.sub_add_cancel ha.le, hcyc]
    rw [e] at hxM
    rcases iterate_T_one_mem (L - a) with e' | e' <;> rw [hxM] at e' <;> omega
  have hxodd : x % 2 = 1 := by
    by_contra hev
    have h1 := hmin 1
    simp only [Function.iterate_one] at h1
    rw [T_of_even (by omega)] at h1
    omega
  have hxC : x ∈ CyclePoints := by
    refine ⟨hm0a, L + oddSteps L x, by omega, ?_⟩
    rw [iterate_C_add_oddSteps, hxper]
  have hxM := cycleMinAbove_29 x hxC hx1 (by omega) (by omega)
  norm_num at hxM
  -- monotone ratio
  have hmono : 293601280 ^ r * (3 * x + 1) ^ r ≤ x ^ r * 880803841 ^ r := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) r
  have hxr : 0 < x ^ r := pow_pos hm0a r
  have key : (2 ^ L * 293601280 ^ r) * x ^ r ≤ 880803841 ^ r * x ^ r := by
    calc (2 ^ L * 293601280 ^ r) * x ^ r = 293601280 ^ r * (2 ^ L * x ^ r) := by ring
      _ ≤ 293601280 ^ r * (3 * x + 1) ^ r := Nat.mul_le_mul_left _ hsand
      _ ≤ x ^ r * 880803841 ^ r := hmono
      _ = 880803841 ^ r * x ^ r := by ring
  have h1 := Nat.le_of_mul_le_mul_right key hxr
  refine ⟨h1, ?_⟩
  have h2 : (880803841 ^ 200) ^ r < (2 ^ 317 * 293601280 ^ 200) ^ r :=
    Nat.pow_lt_pow_left num_step (by omega)
  have h3 : (2 ^ L * 293601280 ^ r) ^ 200 ≤ (880803841 ^ r) ^ 200 := Nat.pow_le_pow_left h1 200
  have h4 : 2 ^ (200 * L) * 293601280 ^ (200 * r) < 2 ^ (317 * r) * 293601280 ^ (200 * r) := by
    calc 2 ^ (200 * L) * 293601280 ^ (200 * r) = (2 ^ L * 293601280 ^ r) ^ 200 := by
          rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ (880803841 ^ r) ^ 200 := h3
      _ = (880803841 ^ 200) ^ r := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ < (2 ^ 317 * 293601280 ^ 200) ^ r := h2
      _ = 2 ^ (317 * r) * 293601280 ^ (200 * r) := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have h5 : 2 ^ (200 * L) < 2 ^ (317 * r) := lt_of_mul_lt_mul_right h4 (Nat.zero_le _)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h5

/-- **Cycle parameters, sharpened.** `cycle_params` plus `200 L < 317 r`. -/
theorem cycle_params' {m L r : ℕ} {v : ℕ → ℕ} (hr : 1 ≤ r) (hv1 : ∀ i < r, 1 ≤ v i)
    (hL : psum v r = L) (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j))
    (hcyc : T^[L] m = m) (hm : m ≠ 1) : L < 2 * r ∧ 40901 ≤ r ∧ 200 * L < 317 * r := by
  obtain ⟨h1, h2⟩ := cycle_params hr hv1 hL hodd hcyc hm
  exact ⟨h1, h2, (cycle_ratio hr hv1 hL hodd hcyc hm).2⟩

/-- Letters of `chr r A` are `≤ 2` when `A < 2r`. -/
theorem chr_le_two {r A : ℕ} (hr0 : 0 < r) (hA : A < 2 * r) (j : ℕ) : NormGoal.chr r A j ≤ 2 := by
  have hc := NormReduce.chr_eq (A := A) hr0 j
  have : A / r ≤ 1 := by
    have := Nat.div_lt_iff_lt_mul hr0 |>.mpr (show A < 2 * r by omega); omega
  split_ifs at hc <;> omega

/-- **Up site of a valid mixed word.** If `r < A < 2r`, the letters of `v` are `≥ 1`,
`psum v r = A`, and the partial sums of `v` are those of `chr r A` plus one at `k` and minus
one at `k'` (`k ≠ k'`), then `k` is an up-site: `r ≤ kA mod r + A mod r`. -/
theorem up_site_of_valid_mixed {r A : ℕ} {v : ℕ → ℕ} (hrA : r < A) (hA : A < 2 * r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = A) {k k' : ℕ} (hk : k < r) (hk'r : k' < r) (hne : k ≠ k')
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) :
    r ≤ k * A % r + A % r := by
  have hr0 : 0 < r := by omega
  have hdiv : A / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hc := NormReduce.chr_eq (A := A) hr0 k
  have hvk := hv1 k hk
  have e1 := hv k hk
  rw [if_pos rfl, if_neg hne] at e1
  have hcs := psum_succ (NormGoal.chr r A) k
  have hvs := psum_succ v k
  rw [hdiv] at hc
  by_cases hk1 : k + 1 = k'
  · have e2 := hv (k + 1) (by omega)
    rw [if_neg (by omega), if_pos hk1] at e2
    have := chr_le_two hr0 hA k
    omega
  · have e2 : (psum v (k + 1) : ℤ) = psum (NormGoal.chr r A) (k + 1) := by
      rcases Nat.lt_or_ge (k + 1) r with h | h
      · have := hv (k + 1) h; rw [if_neg (by omega), if_neg hk1] at this; simpa using this
      · have hk1' : k + 1 = r := by omega
        rw [hk1', hL, NormReduce.psum_chr, Nat.mul_div_cancel_left A hr0]
    split_ifs at hc with h
    · exact h
    · omega

/-- **Down site of a valid mixed word.** Same setting, `0 < k' < r`: `k'` is a down-site,
`k'A mod r < A mod r`. -/
theorem down_site_of_valid_mixed {r A : ℕ} {v : ℕ → ℕ} (hrA : r < A) (hA : A < 2 * r)
    (hv1 : ∀ i < r, 1 ≤ v i) {k k' : ℕ} (hk' : 0 < k' ∧ k' < r) (hne : k ≠ k')
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) :
    k' * A % r < A % r := by
  have hr0 : 0 < r := by omega
  have hdiv : A / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hc := NormReduce.chr_eq (A := A) hr0 (k' - 1)
  have hvk := hv1 (k' - 1) (by omega)
  have e1 := hv k' hk'.2
  rw [if_neg (Ne.symm hne), if_pos rfl] at e1
  have e3 := psum_succ v (k' - 1)
  have e4 := psum_succ (NormGoal.chr r A) (k' - 1)
  rw [Nat.sub_add_cancel hk'.1] at e3 e4
  rw [hdiv] at hc
  have hms := NormReduce.mod_succ (A := A) hr0 (k' - 1)
  rw [Nat.sub_add_cancel hk'.1] at hms
  have := Nat.mod_lt ((k' - 1) * A) hr0
  by_cases hk1 : k' - 1 = k
  · have e2 := hv (k' - 1) (by omega)
    rw [if_pos hk1, if_neg (by omega)] at e2
    have := chr_le_two hr0 hA (k' - 1)
    omega
  · have e2 := hv (k' - 1) (by omega)
    rw [if_neg hk1, if_neg (by omega)] at e2
    split_ifs at hc with h
    · rw [if_pos h] at hms; omega
    · omega

/-- **Cycle-length window and the vacuity of `NormMixedRev.cycle_mixed_flips_rev`.**
The hypotheses of `NormMixedRev.cycle_mixed_flips_rev` (even without `gcd(L, r) = 1`) are
never satisfied by an actual cycle: validity puts `ρ = kL mod r ≥ r - a` and
`ρ' = k'L mod r < a` (`a = L - r`), and `200L < 317r` (`cycle_ratio`) gives
`ρ' > ρ > 0.415 r`, while `H4` forces `4^{(ρ'+1)/r} ≤ 29/25`, i.e. `ρ' + 1 < 0.116 r`.
So that theorem is cycle-vacuous. (Proof does not use the norm engine.) -/
theorem cycle_mixed_flips_rev_vacuous {m L r : ℕ} {v : ℕ → ℕ}
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (_H1 : 2 ≤ k * L % r) (H2 : k * L % r + 3 ≤ k' * L % r)
    (_H3 : k' * L % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * L % r + 1 : ℕ) : ℝ) / r) +
      24 * (4:ℝ) ^ (((k' * L % r - k * L % r : ℕ) : ℝ) / r) ≤ 149 / 5)
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r L) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) : False := by
  obtain ⟨hL2, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨_, h200⟩ := cycle_ratio (by omega) hv1 hL hodd hcyc hm
  obtain ⟨hq, _⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  have hrL := NormReduce.r_lt_A hq
  have hup := up_site_of_valid_mixed hrL hL2 hv1 hL hk.2 hk'.2 hne hv
  have hdn := down_site_of_valid_mixed hrL hL2 hv1 hk' hne hv
  have hmodL : L % r = L - r := by
    rw [Nat.mod_eq_sub_mod hrL.le, Nat.mod_eq_of_lt (by omega)]
  -- analytic part
  set s := k' * L % r + 1 with hs
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hb : (1:ℝ) ≤ (4:ℝ) ^ (((k' * L % r - k * L % r : ℕ) : ℝ) / r) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have h4 : (4:ℝ) ^ ((s:ℝ) / r) ≤ 29 / 25 := by linarith
  rw [Real.rpow_def_of_pos (by norm_num)] at h4
  have he := Real.add_one_le_exp (Real.log 4 * ((s:ℝ) / r))
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hy : Real.log 4 * ((s:ℝ) / r) ≤ 4 / 25 := by linarith
  have hy2 : (s:ℝ) / r * (1386 / 1000) ≤ 4 / 25 := by
    have : (0:ℝ) ≤ (s:ℝ) / r := by positivity
    nlinarith
  have hy3 : (s:ℝ) * 1386 ≤ 160 * r := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hr0] at hy2; linarith
  have hy4 : s * 1386 ≤ 160 * r := by exact_mod_cast hy3
  omega

end Collatz.NormGeom

#print axioms Collatz.NormGeom.num_step
#print axioms Collatz.NormGeom.cycle_ratio
#print axioms Collatz.NormGeom.cycle_params'
#print axioms Collatz.NormGeom.up_site_of_valid_mixed
#print axioms Collatz.NormGeom.down_site_of_valid_mixed
#print axioms Collatz.NormGeom.cycle_mixed_flips_rev_vacuous
