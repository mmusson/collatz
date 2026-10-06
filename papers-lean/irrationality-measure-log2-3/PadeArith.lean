import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# Arithmetic of the 4-root Hata-type family

`V_n(X) = (X-1)^{4n} (2X-3)^{2n} (3X-4)^{3n} (5X-6)^n ∈ ℤ[X]`, with coefficients `w_i`.
Unconditional, elementary:
* `vp_C1`: `3^{3n-i} ∣ w_i`;  `vp_C2`: `2^{i-8n} ∣ w_i`;  `vp_C3`: `3^{i-7n} ∣ w_i`;
  `vp_C4`: `2^{7n-2i} ∣ w_i`  (truncated subtraction in ℕ).
  Proof: per-linear-factor divisibility profiles (`LowDiv`/`HighDiv`) are multiplicative
  (`LowDiv.mul`, `.pow`, `HighDiv.mul`, `.pow`).
* `integral_term`: with `K = 5n`, `D_n = 2^{3n} 3^{2n} lcm(1..5n)`, for `i ≤ 10n`, `i ≠ 5n`,
  `s ∈ {3/2, 4/3}`: `D_n w_i s^{i-K}/(i-K) ∈ ℤ`.  `integral_term_one`: `D_n w_i/(i-K) ∈ ℤ`.
These are the denominator facts for `E_j = ∫_1^{s_j} V_n(u) u^{-5n-1} du
= w_K log s_j + Σ_{i≠K} w_i (s_j^{i-K}-1)/(i-K)`; the integral identity, the sup bound and
the non-vanishing `Δ_n ≠ 0` are NOT formalized.
-/

open Polynomial

namespace Collatz.PadeArith

/-- `c^{e - w i} ∣ P_i` for all `i` (low-degree coefficients carry powers of `c`). -/
def LowDiv (c : ℤ) (w e : ℕ) (P : ℤ[X]) : Prop := ∀ i, c^(e - w*i) ∣ P.coeff i
/-- `c^{w i - e} ∣ P_i` for all `i` (high-degree coefficients carry powers of `c`). -/
def HighDiv (c : ℤ) (w e : ℕ) (P : ℤ[X]) : Prop := ∀ i, c^(w*i - e) ∣ P.coeff i

theorem LowDiv.mul {c : ℤ} {w e₁ e₂ : ℕ} {P R : ℤ[X]} (hP : LowDiv c w e₁ P) (hR : LowDiv c w e₂ R) :
    LowDiv c w (e₁+e₂) (P*R) := by
  intro k
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  have h1 : c^(e₁+e₂ - w*k) ∣ c^((e₁ - w*x.1) + (e₂ - w*x.2)) := by
    apply pow_dvd_pow
    rw [← hx, mul_add]; omega
  exact h1.trans (by rw [pow_add]; exact mul_dvd_mul (hP _) (hR _))

theorem HighDiv.mul {c : ℤ} {w e₁ e₂ : ℕ} {P R : ℤ[X]} (hP : HighDiv c w e₁ P) (hR : HighDiv c w e₂ R) :
    HighDiv c w (e₁+e₂) (P*R) := by
  intro k
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  have h1 : c^(w*k - (e₁+e₂)) ∣ c^((w*x.1 - e₁) + (w*x.2 - e₂)) := by
    apply pow_dvd_pow
    rw [← hx, mul_add]; omega
  exact h1.trans (by rw [pow_add]; exact mul_dvd_mul (hP _) (hR _))

theorem lowDiv_one {c : ℤ} {w : ℕ} : LowDiv c w 0 1 := by
  intro i; simp

theorem highDiv_one {c : ℤ} {w : ℕ} : HighDiv c w 0 1 := by
  intro i
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · exact dvd_zero _

theorem lowDiv_zero {c : ℤ} {w : ℕ} (P : ℤ[X]) : LowDiv c w 0 P := by
  intro i; simp

theorem LowDiv.pow {c : ℤ} {w e : ℕ} {P : ℤ[X]} (hP : LowDiv c w e P) (k : ℕ) :
    LowDiv c w (k*e) (P^k) := by
  induction k with
  | zero => simpa using (lowDiv_one (c := c) (w := w))
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]; exact ih.mul hP

theorem HighDiv.pow {c : ℤ} {w e : ℕ} {P : ℤ[X]} (hP : HighDiv c w e P) (k : ℕ) :
    HighDiv c w (k*e) (P^k) := by
  induction k with
  | zero => simpa using (highDiv_one (c := c) (w := w))
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]; exact ih.mul hP

theorem coeff_linear (a b : ℤ) (i : ℕ) :
    (C a * X - C b).coeff i = if i = 0 then -b else if i = 1 then a else 0 := by
  rw [coeff_sub, coeff_C_mul_X, coeff_C]
  rcases i with _ | _ | i <;> simp

theorem lowDiv_linear {c : ℤ} {w e : ℕ} (a b : ℤ) (h : c^e ∣ b) (hew : e ≤ w) :
    LowDiv c w e (C a * X - C b) := by
  intro i
  rw [coeff_linear]
  rcases i with _ | i
  · simpa using h
  · have : e - w * (i+1) = 0 := by
      have : w ≤ w * (i+1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [this, pow_zero]; exact one_dvd _

theorem highDiv_linear {c : ℤ} {w e : ℕ} (a b : ℤ) (h : c^(w-e) ∣ a) :
    HighDiv c w e (C a * X - C b) := by
  intro i
  rw [coeff_linear]
  rcases i with _ | _ | i
  · simp
  · simpa using h
  · simp

/-- The 4-root Hata-type polynomial `V_n`. -/
noncomputable def Vp (n : ℕ) : ℤ[X] :=
  (X - C 1)^(4*n) * (C 2 * X - C 3)^(2*n) * (C 3 * X - C 4)^(3*n) * (C 5 * X - C 6)^n

theorem X_sub_C_eq : (X - C (1:ℤ)) = C 1 * X - C 1 := by simp

theorem vp_C1 (n : ℕ) : ∀ i, (3:ℤ)^(3*n - i) ∣ (Vp n).coeff i := by
  have hA : LowDiv 3 1 0 (X - C 1) := lowDiv_zero _
  have hB : LowDiv 3 1 1 (C 2 * X - C 3) := lowDiv_linear _ _ (by norm_num) le_rfl
  have hG : LowDiv 3 1 0 (C 3 * X - C 4) := lowDiv_zero _
  have hH : LowDiv 3 1 1 (C 5 * X - C 6) := lowDiv_linear _ _ (by norm_num) le_rfl
  have := (((hA.pow (4*n)).mul (hB.pow (2*n))).mul (hG.pow (3*n))).mul (hH.pow n)
  intro i
  have h := this i
  have e : 4 * n * 0 + 2 * n * 1 + 3 * n * 0 + n * 1 - 1 * i = 3*n - i := by omega
  rw [e] at h; exact h

theorem vp_C2 (n : ℕ) : ∀ i, (2:ℤ)^(i - 8*n) ∣ (Vp n).coeff i := by
  have hA : HighDiv 2 1 1 (X - C 1) := by
    rw [X_sub_C_eq]; exact highDiv_linear _ _ (by norm_num)
  have hB : HighDiv 2 1 0 (C 2 * X - C 3) := highDiv_linear _ _ (by norm_num)
  have hG : HighDiv 2 1 1 (C 3 * X - C 4) := highDiv_linear _ _ (by norm_num)
  have hH : HighDiv 2 1 1 (C 5 * X - C 6) := highDiv_linear _ _ (by norm_num)
  have := (((hA.pow (4*n)).mul (hB.pow (2*n))).mul (hG.pow (3*n))).mul (hH.pow n)
  intro i
  have h := this i
  have e : 1 * i - (4 * n * 1 + 2 * n * 0 + 3 * n * 1 + n * 1) = i - 8*n := by omega
  rw [e] at h; exact h

theorem vp_C3 (n : ℕ) : ∀ i, (3:ℤ)^(i - 7*n) ∣ (Vp n).coeff i := by
  have hA : HighDiv 3 1 1 (X - C 1) := by
    rw [X_sub_C_eq]; exact highDiv_linear _ _ (by norm_num)
  have hB : HighDiv 3 1 1 (C 2 * X - C 3) := highDiv_linear _ _ (by norm_num)
  have hG : HighDiv 3 1 0 (C 3 * X - C 4) := highDiv_linear _ _ (by norm_num)
  have hH : HighDiv 3 1 1 (C 5 * X - C 6) := highDiv_linear _ _ (by norm_num)
  have := (((hA.pow (4*n)).mul (hB.pow (2*n))).mul (hG.pow (3*n))).mul (hH.pow n)
  intro i
  have h := this i
  have e : 1 * i - (4 * n * 1 + 2 * n * 1 + 3 * n * 0 + n * 1) = i - 7*n := by omega
  rw [e] at h; exact h

theorem vp_C4 (n : ℕ) : ∀ i, (2:ℤ)^(7*n - 2*i) ∣ (Vp n).coeff i := by
  have hA : LowDiv 2 2 0 (X - C 1) := lowDiv_zero _
  have hB : LowDiv 2 2 0 (C 2 * X - C 3) := lowDiv_zero _
  have hG : LowDiv 2 2 2 (C 3 * X - C 4) := lowDiv_linear _ _ (by norm_num) le_rfl
  have hH : LowDiv 2 2 1 (C 5 * X - C 6) := lowDiv_linear _ _ (by norm_num) (by norm_num)
  have := (((hA.pow (4*n)).mul (hB.pow (2*n))).mul (hG.pow (3*n))).mul (hH.pow n)
  intro i
  have h := this i
  have e : 4 * n * 0 + 2 * n * 0 + 3 * n * 2 + n * 1 - 2 * i = 7*n - 2*i := by omega
  rw [e] at h; exact h


/-- `lcm(1,…,5n)`. -/
def Lcm5 (n : ℕ) : ℕ := (Finset.Icc 1 (5*n)).lcm id

/-- `D_n = 2^{3n} 3^{2n} lcm(1..5n)`. -/
def Dn (n : ℕ) : ℤ := 2^(3*n) * 3^(2*n) * (Lcm5 n : ℤ)

theorem dvd_lcm5 {n j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 5*n) : j ∣ Lcm5 n := by
  have := Finset.dvd_lcm (s := Finset.Icc 1 (5*n)) (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  unfold Lcm5; exact this

theorem dvd_hi_two (n j : ℕ) : (2:ℤ)^j ∣ 2^(3*n) * (Vp n).coeff (5*n+j) := by
  have h := vp_C2 n (5*n+j)
  have : (2:ℤ)^j ∣ 2^(3*n) * 2^(5*n+j-8*n) := by
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

theorem dvd_hi_three (n j : ℕ) : (3:ℤ)^j ∣ 3^(2*n) * (Vp n).coeff (5*n+j) := by
  have h := vp_C3 n (5*n+j)
  have : (3:ℤ)^j ∣ 3^(2*n) * 3^(5*n+j-7*n) := by
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

theorem dvd_lo_three {n i j : ℕ} (hj : i + j = 5*n) : (3:ℤ)^j ∣ 3^(2*n) * (Vp n).coeff i := by
  have h := vp_C1 n i
  have : (3:ℤ)^j ∣ 3^(2*n) * 3^(3*n-i) := by
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

theorem dvd_lo_four {n i j : ℕ} (hj : i + j = 5*n) : (4:ℤ)^j ∣ 2^(3*n) * (Vp n).coeff i := by
  have h := vp_C4 n i
  have : (4:ℤ)^j ∣ 2^(3*n) * 2^(7*n-2*i) := by
    rw [← pow_add, show (4:ℤ) = 2^2 by norm_num, ← pow_mul]; exact pow_dvd_pow _ (by omega)
  exact this.trans (mul_dvd_mul_left _ h)

/-- `D_n w_i s^{i-5n}/(i-5n)` is an integer for `i ≤ 10n`, `i ≠ 5n`, `s ∈ {3/2,4/3}`. -/
theorem integral_term (n i : ℕ) (hi : i ≤ 10*n) (hK : i ≠ 5*n) (s : ℚ) (hs : s = 3/2 ∨ s = 4/3) :
    ∃ z : ℤ, (Dn n : ℚ) * ((Vp n).coeff i : ℚ) * s^((i:ℤ) - 5*n) / ((i:ℚ) - 5*n) = z := by
  rcases lt_or_gt_of_ne hK with hlt | hgt
  · obtain ⟨j, hj⟩ : ∃ j, i + j = 5*n := ⟨5*n - i, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5 (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hexp : (i:ℤ) - 5*n = -(j:ℤ) := by omega
    have hden : (i:ℚ) - 5*n = -(j:ℚ) := by
      have : (i:ℚ) + j = 5*n := by exact_mod_cast hj
      linarith
    rw [hexp, hden, zpow_neg, zpow_natCast]
    unfold Dn; rw [hm]
    rcases hs with rfl | rfl
    · obtain ⟨u, hu⟩ := dvd_lo_three (n := n) hj
      have hu' : (3:ℚ)^(2*n) * ((Vp n).coeff i : ℚ) = 3^j * u := by exact_mod_cast hu
      refine ⟨-(m * 2^(3*n) * 2^j * u), ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (-(m:ℚ)) * hu'
    · obtain ⟨u, hu⟩ := dvd_lo_four (n := n) hj
      have hu' : (2:ℚ)^(3*n) * ((Vp n).coeff i : ℚ) = 4^j * u := by exact_mod_cast hu
      refine ⟨-(m * 3^(2*n) * 3^j * u), ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (-(m:ℚ)) * hu'
  · obtain ⟨j, rfl⟩ : ∃ j, i = 5*n + j := ⟨i - 5*n, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5 (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hexp : ((5*n+j : ℕ):ℤ) - 5*n = (j:ℤ) := by push_cast; ring
    have hden : ((5*n+j : ℕ):ℚ) - 5*n = (j:ℚ) := by push_cast; ring
    rw [hexp, hden, zpow_natCast]
    unfold Dn; rw [hm]
    rcases hs with rfl | rfl
    · obtain ⟨u, hu⟩ := dvd_hi_two n j
      have hu' : (2:ℚ)^(3*n) * ((Vp n).coeff (5*n+j) : ℚ) = 2^j * u := by exact_mod_cast hu
      refine ⟨m * 3^(2*n) * 3^j * u, ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (m:ℚ) * hu'
    · obtain ⟨u, hu⟩ := dvd_hi_three n j
      have hu' : (3:ℚ)^(2*n) * ((Vp n).coeff (5*n+j) : ℚ) = 3^j * u := by exact_mod_cast hu
      refine ⟨m * 2^(3*n) * 4^j * u, ?_⟩
      push_cast
      rw [div_pow]
      field_simp
      linear_combination (m:ℚ) * hu'

/-- `D_n w_i/(i-5n)` is an integer for `i ≤ 10n`, `i ≠ 5n`. -/
theorem integral_term_one (n i : ℕ) (hi : i ≤ 10*n) (hK : i ≠ 5*n) :
    ∃ z : ℤ, (Dn n : ℚ) * ((Vp n).coeff i : ℚ) / ((i:ℚ) - 5*n) = z := by
  rcases lt_or_gt_of_ne hK with hlt | hgt
  · obtain ⟨j, hj⟩ : ∃ j, i + j = 5*n := ⟨5*n - i, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5 (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hden : (i:ℚ) - 5*n = -(j:ℚ) := by
      have : (i:ℚ) + j = 5*n := by exact_mod_cast hj
      linarith
    rw [hden]
    refine ⟨-(2^(3*n) * 3^(2*n) * m * (Vp n).coeff i), ?_⟩
    unfold Dn; rw [hm]; push_cast
    field_simp
  · obtain ⟨j, rfl⟩ : ∃ j, i = 5*n + j := ⟨i - 5*n, by omega⟩
    obtain ⟨m, hm⟩ := dvd_lcm5 (n := n) (j := j) (by omega) (by omega)
    have hj0 : (j:ℚ) ≠ 0 := by
      have : j ≠ 0 := by omega
      exact_mod_cast this
    have hden : ((5*n+j : ℕ):ℚ) - 5*n = (j:ℚ) := by push_cast; ring
    rw [hden]
    refine ⟨2^(3*n) * 3^(2*n) * m * (Vp n).coeff (5*n+j), ?_⟩
    unfold Dn; rw [hm]; push_cast
    field_simp

end Collatz.PadeArith

#print axioms Collatz.PadeArith.vp_C1
#print axioms Collatz.PadeArith.vp_C2
#print axioms Collatz.PadeArith.vp_C3
#print axioms Collatz.PadeArith.vp_C4
#print axioms Collatz.PadeArith.integral_term
#print axioms Collatz.PadeArith.integral_term_one
