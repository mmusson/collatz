import CollatzSearch.PadeBounds

/-!
# Arithmetic of the sign-split family `Vq_n = Vp_n (5X-6)`
(side project, NOT Goal progress; `no_nontrivial_cycles` remains OPEN)

`Vq_n = (X-1)^{4n}(2X-3)^{2n}(3X-4)^{3n}(5X-6)^{n+1} ∈ ℤ[X]`, coefficients `u_i`.
Unconditional, elementary (truncated ℕ subtraction in exponents):
* `vq_C1`: `3^{3n+1-i} ∣ u_i`; `vq_C2`: `2^{i-8n-1} ∣ u_i`; `vq_C3`: `3^{i-7n-1} ∣ u_i`;
  `vq_C4`: `2^{7n+1-2i} ∣ u_i` (`PadeArith`/`TypeIITransfer` profiles of `Vp` times the profile of `5X-6`).
* `integral_term_q`, `integral_term_one_q`: with `K = 5n`,
  `D'_n = 2^{3n+1} 3^{2n+1} lcm(1..5n+1)`, for `i ≤ 10n+1`, `i ≠ 5n`, `s ∈ {3/2, 4/3}`:
  `D'_n u_i s^{i-K}/(i-K) ∈ ℤ` and `D'_n u_i/(i-K) ∈ ℤ`.
* `natDegree_Vq_le`: `natDegree Vq_n ≤ 10n+1`;
  `coeff_Vq_abs_le`: `|u_i| ≤ 11·2^{4n}5^{2n}7^{3n}11^n`.
These are the denominator/size facts for the `SignApprox` witness candidate (see
`SignSplit.lean`, `PadeSign.lean`); the sup bound and the lower bound for `|E1|` are NOT
formalized, so no `SignApprox` witness exists yet.
-/

open Polynomial

namespace CollatzSearch.PadeArithQ
open PadeArith

/-- `Vq_n = Vp_n (5X-6) = (X-1)^{4n}(2X-3)^{2n}(3X-4)^{3n}(5X-6)^{n+1}`. -/
noncomputable def Vq (n : ℕ) : ℤ[X] := Vp n * (C 5 * X - C 6)

/-- Product form of `Vq_n`. -/
theorem Vq_eq (n : ℕ) : Vq n =
    (X - C 1)^(4*n) * (C 2 * X - C 3)^(2*n) * (C 3 * X - C 4)^(3*n) * (C 5 * X - C 6)^(n+1) := by
  unfold Vq Vp; ring

/-- `3^{3n+1-i}` divides the `i`-th coefficient of `Vq_n`. -/
theorem vq_C1 (n : ℕ) : ∀ i, (3:ℤ)^(3*n+1 - i) ∣ (Vq n).coeff i := by
  have hV : LowDiv 3 1 (3*n) (Vp n) := fun i => by rw [one_mul]; exact vp_C1 n i
  have hH : LowDiv 3 1 1 (C 5 * X - C 6) := lowDiv_linear _ _ (by norm_num) le_rfl
  intro i
  have h := hV.mul hH i
  rw [one_mul] at h; exact h

/-- `2^{i-(8n+1)}` divides the `i`-th coefficient of `Vq_n`. -/
theorem vq_C2 (n : ℕ) : ∀ i, (2:ℤ)^(i - (8*n+1)) ∣ (Vq n).coeff i := by
  have hV : HighDiv 2 1 (8*n) (Vp n) := fun i => by rw [one_mul]; exact vp_C2 n i
  have hH : HighDiv 2 1 1 (C 5 * X - C 6) := highDiv_linear _ _ (by norm_num)
  intro i
  have h := hV.mul hH i
  rw [one_mul] at h; exact h

/-- `3^{i-(7n+1)}` divides the `i`-th coefficient of `Vq_n`. -/
theorem vq_C3 (n : ℕ) : ∀ i, (3:ℤ)^(i - (7*n+1)) ∣ (Vq n).coeff i := by
  have hV : HighDiv 3 1 (7*n) (Vp n) := fun i => by rw [one_mul]; exact vp_C3 n i
  have hH : HighDiv 3 1 1 (C 5 * X - C 6) := highDiv_linear _ _ (by norm_num)
  intro i
  have h := hV.mul hH i
  rw [one_mul] at h; exact h

/-- `2^{7n+1-2i}` divides the `i`-th coefficient of `Vq_n`. -/
theorem vq_C4 (n : ℕ) : ∀ i, (2:ℤ)^(7*n+1 - 2*i) ∣ (Vq n).coeff i := by
  have hV : LowDiv 2 2 (7*n) (Vp n) := fun i => vp_C4 n i
  have hH : LowDiv 2 2 1 (C 5 * X - C 6) := lowDiv_linear _ _ (by norm_num) (by norm_num)
  intro i
  exact hV.mul hH i

/-- `lcm(1,…,5n+1)`. -/
def Lcm5q (n : ℕ) : ℕ := (Finset.Icc 1 (5*n+1)).lcm id

/-- `D'_n = 2^{3n+1} 3^{2n+1} lcm(1..5n+1)`. -/
def Dq (n : ℕ) : ℤ := 2^(3*n+1) * 3^(2*n+1) * (Lcm5q n : ℤ)

theorem dvd_lcm5q {n j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 5*n+1) : j ∣ Lcm5q n := by
  have := Finset.dvd_lcm (s := Finset.Icc 1 (5*n+1)) (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  unfold Lcm5q; exact this

theorem dvd_hi_two_q (n j : ℕ) : (2:ℤ)^j ∣ 2^(3*n+1) * (Vq n).coeff (5*n+j) := by
  have h := vq_C2 n (5*n+j)
  have : (2:ℤ)^j ∣ 2^(3*n+1) * 2^(5*n+j-(8*n+1)) := by
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

theorem dvd_hi_three_q (n j : ℕ) : (3:ℤ)^j ∣ 3^(2*n+1) * (Vq n).coeff (5*n+j) := by
  have h := vq_C3 n (5*n+j)
  have : (3:ℤ)^j ∣ 3^(2*n+1) * 3^(5*n+j-(7*n+1)) := by
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

theorem dvd_lo_three_q {n i j : ℕ} (hj : i + j = 5*n) :
    (3:ℤ)^j ∣ 3^(2*n+1) * (Vq n).coeff i := by
  have h := vq_C1 n i
  have : (3:ℤ)^j ∣ 3^(2*n+1) * 3^(3*n+1-i) := by
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

theorem dvd_lo_four_q {n i j : ℕ} (hj : i + j = 5*n) :
    (4:ℤ)^j ∣ 2^(3*n+1) * (Vq n).coeff i := by
  have h := vq_C4 n i
  have : (4:ℤ)^j ∣ 2^(3*n+1) * 2^(7*n+1-2*i) := by
    rw [← pow_add, show (4:ℤ) = 2^2 by norm_num, ← pow_mul]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

/-- `D'_n u_i s^{i-5n}/(i-5n) ∈ ℤ` for `i ≤ 10n+1`, `i ≠ 5n`, `s ∈ {3/2, 4/3}`. -/
theorem integral_term_q (n i : ℕ) (hi : i ≤ 10*n+1) (hK : i ≠ 5*n) (s : ℚ)
    (hs : s = 3/2 ∨ s = 4/3) :
    ∃ z : ℤ, (Dq n : ℚ) * ((Vq n).coeff i : ℚ) * s^((i:ℤ) - 5*n) / ((i:ℚ) - 5*n) = z := by
  rcases lt_or_gt_of_ne hK with hlt | hgt
  · obtain ⟨j, hj⟩ : ∃ j, i + j = 5*n := ⟨5*n - i, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5q (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hexp : (i:ℤ) - 5*n = -(j:ℤ) := by omega
    have hden : (i:ℚ) - 5*n = -(j:ℚ) := by
      have : (i:ℚ) + j = 5*n := by exact_mod_cast hj
      linarith
    rw [hexp, hden, zpow_neg, zpow_natCast]
    unfold Dq; rw [hm]
    rcases hs with rfl | rfl
    · obtain ⟨u, hu⟩ := dvd_lo_three_q (n := n) hj
      have hu' : (3:ℚ)^(2*n+1) * ((Vq n).coeff i : ℚ) = 3^j * u := by exact_mod_cast hu
      refine ⟨-(m * 2^(3*n+1) * 2^j * u), ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (-(m:ℚ)) * hu'
    · obtain ⟨u, hu⟩ := dvd_lo_four_q (n := n) hj
      have hu' : (2:ℚ)^(3*n+1) * ((Vq n).coeff i : ℚ) = 4^j * u := by exact_mod_cast hu
      refine ⟨-(m * 3^(2*n+1) * 3^j * u), ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (-(m:ℚ)) * hu'
  · obtain ⟨j, rfl⟩ : ∃ j, i = 5*n + j := ⟨i - 5*n, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5q (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hexp : ((5*n+j : ℕ):ℤ) - 5*n = (j:ℤ) := by push_cast; ring
    have hden : ((5*n+j : ℕ):ℚ) - 5*n = (j:ℚ) := by push_cast; ring
    rw [hexp, hden, zpow_natCast]
    unfold Dq; rw [hm]
    rcases hs with rfl | rfl
    · obtain ⟨u, hu⟩ := dvd_hi_two_q n j
      have hu' : (2:ℚ)^(3*n+1) * ((Vq n).coeff (5*n+j) : ℚ) = 2^j * u := by exact_mod_cast hu
      refine ⟨m * 3^(2*n+1) * 3^j * u, ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (m:ℚ) * hu'
    · obtain ⟨u, hu⟩ := dvd_hi_three_q n j
      have hu' : (3:ℚ)^(2*n+1) * ((Vq n).coeff (5*n+j) : ℚ) = 3^j * u := by exact_mod_cast hu
      refine ⟨m * 2^(3*n+1) * 4^j * u, ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (m:ℚ) * hu'

/-- `D'_n u_i/(i-5n) ∈ ℤ` for `i ≤ 10n+1`, `i ≠ 5n`. -/
theorem integral_term_one_q (n i : ℕ) (hi : i ≤ 10*n+1) (hK : i ≠ 5*n) :
    ∃ z : ℤ, (Dq n : ℚ) * ((Vq n).coeff i : ℚ) / ((i:ℚ) - 5*n) = z := by
  rcases lt_or_gt_of_ne hK with hlt | hgt
  · obtain ⟨j, hj⟩ : ∃ j, i + j = 5*n := ⟨5*n - i, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5q (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hden : (i:ℚ) - 5*n = -(j:ℚ) := by
      have : (i:ℚ) + j = 5*n := by exact_mod_cast hj
      linarith
    rw [hden]
    refine ⟨-(2^(3*n+1) * 3^(2*n+1) * m * (Vq n).coeff i), ?_⟩
    unfold Dq; rw [hm]; push_cast
    field_simp
  · obtain ⟨j, rfl⟩ : ∃ j, i = 5*n + j := ⟨i - 5*n, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5q (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hden : ((5*n+j : ℕ):ℚ) - 5*n = (j:ℚ) := by push_cast; ring
    rw [hden]
    refine ⟨2^(3*n+1) * 3^(2*n+1) * m * (Vq n).coeff (5*n+j), ?_⟩
    unfold Dq; rw [hm]; push_cast
    field_simp

/-- `natDegree Vq_n ≤ 10n+1`. -/
theorem natDegree_Vq_le (n : ℕ) : (Vq n).natDegree ≤ 10*n+1 := by
  unfold Vq
  have h1 := natDegree_Vp_le n
  have h2 := natDegree_linear_le' 5 6
  have := natDegree_mul_le (p := Vp n) (q := C 5 * X - C 6)
  omega

/-- `Vq_n` is coefficientwise dominated by `Wp_n (5X+6)`. -/
theorem dom_Vq (n : ℕ) : Dom (Vq n) (Wp n * (C 5 * X + C 6)) :=
  (dom_Vp n).mul (dom_linear 5 6 (by norm_num) (by norm_num))

/-- `|u_i| ≤ 11 · 2^{4n} 5^{2n} 7^{3n} 11^n` for every coefficient of `Vq_n`. -/
theorem coeff_Vq_abs_le (n i : ℕ) :
    |(Vq n).coeff i| ≤ 11 * (2^(4*n) * 5^(2*n) * 7^(3*n) * 11^n) := by
  have e : (Wp n * (C 5 * X + C 6)).eval 1 = 11 * (2^(4*n) * 5^(2*n) * 7^(3*n) * 11^n) := by
    rw [eval_mul, eval_one_Wp]; simp; ring
  rw [← e]
  exact le_trans (dom_Vq n i) (coeff_le_eval_one (dom_Vq n).nonneg i)

end CollatzSearch.PadeArithQ

#print axioms CollatzSearch.PadeArithQ.Vq_eq
#print axioms CollatzSearch.PadeArithQ.vq_C1
#print axioms CollatzSearch.PadeArithQ.vq_C2
#print axioms CollatzSearch.PadeArithQ.vq_C3
#print axioms CollatzSearch.PadeArithQ.vq_C4
#print axioms CollatzSearch.PadeArithQ.integral_term_q
#print axioms CollatzSearch.PadeArithQ.integral_term_one_q
#print axioms CollatzSearch.PadeArithQ.natDegree_Vq_le
#print axioms CollatzSearch.PadeArithQ.coeff_Vq_abs_le
