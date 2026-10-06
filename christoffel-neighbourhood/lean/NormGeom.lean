import NormBig
import NormCycleAll

/-!
# cycle geometry: the ratio window `200 L < 317 r`

* `cycle_ratio`: every nontrivial positive `T`-cycle (odd point `m ≠ 1`, period `L`, `r` odd
  steps) satisfies `2^L · M^r ≤ (3M+1)^r` with `M = 293601280` (the Crandall sandwich at the
  cycle minimum `x ≥ M`, `cycleMinAbove_29`, and monotonicity of `(3x+1)/x`), hence
  `200 L < 317 r` (`(3M+1)^200 < 2^317 M^200`, a kernel `decide` on ~1700-digit naturals).
  `cycle_params'` packages `L < 2r`, `r ≥ 40901`, `200L < 317r`.

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

end Collatz.NormGeom

#print axioms Collatz.NormGeom.num_step
#print axioms Collatz.NormGeom.cycle_ratio
#print axioms Collatz.NormGeom.cycle_params'