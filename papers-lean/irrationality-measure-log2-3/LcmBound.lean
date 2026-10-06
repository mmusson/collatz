import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import PadeArith

/-!
# `lcm(1,…,N) ≤ 4^N` (classical Chebyshev-type bound)

Mathlib (this toolchain) has no such bound (grep for lcm + centralBinom/four_pow found nothing).
* `Lc_dvd`: for `a ≤ b`, `lcm(1..b+a) ∣ lcm(1..b) · C(b+a, a)` (per prime: a prime power
  `p^e ∈ (b, b+a]` forces a carry at digit `e` in `a + b` base `p`, Kummer via
  `Nat.factorization_choose'`, and `p^{e-1} ≤ b`).
* `Lc_le_four_pow`: `lcm(1..N) ≤ 4^N` (strong induction, `C(2m,m), C(2m+1,m) ≤ 4^m`).
* `Dn_le`: `D_n = 2^{3n} 3^{2n} lcm(1..5n) ≤ 73728^n` for the T1 family.
-/

namespace Collatz.LcmBound

/-- `lcm(1,…,N)`. -/
def Lc (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

theorem dvd_Lc {j N : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ N) : j ∣ Lc N := by
  have := Finset.dvd_lcm (s := Finset.Icc 1 N) (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  unfold Lc; exact this

theorem Lc_ne_zero (N : ℕ) : Lc N ≠ 0 := by
  unfold Lc
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

theorem Lc_dvd (a b : ℕ) (hab : a ≤ b) : Lc (b+a) ∣ Lc b * Nat.choose (b+a) a := by
  unfold Lc
  apply Finset.lcm_dvd
  intro j hj
  rw [Finset.mem_Icc] at hj
  simp only [id]
  have hC : Nat.choose (b+a) a ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hX : Lc b * Nat.choose (b+a) a ≠ 0 := mul_ne_zero (Lc_ne_zero b) hC
  change j ∣ Lc b * Nat.choose (b+a) a
  rw [← Nat.factorization_prime_le_iff_dvd (by omega) hX]
  intro p hp
  set e := j.factorization p with he_def
  have hpe : p^e ∣ j := Nat.ordProj_dvd j p
  have hpej : p^e ≤ j := Nat.le_of_dvd (by omega) hpe
  have hp1 : 1 ≤ p^e := Nat.one_le_pow _ _ hp.pos
  rw [Nat.factorization_mul (Lc_ne_zero b) hC, Finsupp.add_apply]
  by_cases hle : p^e ≤ b
  · have := (hp.pow_dvd_iff_le_factorization (Lc_ne_zero b)).mp (dvd_Lc hp1 hle)
    omega
  · push Not at hle
    have he : 1 ≤ e := by
      by_contra hcon
      have : e = 0 := by omega
      rw [this, pow_zero] at hle
      omega
    have h1 : p^(e-1) ≤ b := by
      have e1 : p^e = p * p^(e-1) := by rw [← pow_succ']; congr 1; omega
      have : 2 * p^(e-1) ≤ p^e := by rw [e1]; exact Nat.mul_le_mul_right _ hp.two_le
      omega
    have hA : e - 1 ≤ (Lc b).factorization p :=
      (hp.pow_dvd_iff_le_factorization (Lc_ne_zero b)).mp
        (dvd_Lc (Nat.one_le_pow _ _ hp.pos) h1)
    have hB : 1 ≤ (Nat.choose (b+a) a).factorization p := by
      rw [Nat.factorization_choose' (n := b) (k := a) hp (Nat.lt_succ_self _)]
      apply Finset.card_pos.mpr
      refine ⟨e, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_Ico]
      have hel : e ≤ Nat.log p (b+a) := Nat.le_log_of_pow_le hp.one_lt (by omega)
      refine ⟨⟨he, by omega⟩, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega : a < p^e), Nat.mod_eq_of_lt hle]
      omega
    omega

/-- **Classical (Chebyshev-type)**: `lcm(1,…,N) ≤ 4^N`. -/
theorem Lc_le_four_pow (N : ℕ) : Lc N ≤ 4^N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 2 with hN | hN
    · interval_cases N <;> decide
    · rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
      · have hd := Lc_dvd m m le_rfl
        have hle := Nat.le_of_dvd (mul_pos (Nat.pos_of_ne_zero (Lc_ne_zero m))
          (Nat.choose_pos (by omega))) hd
        have hc : Nat.choose (m+m) m ≤ 4^m := by
          rw [← two_mul]; exact Nat.centralBinom_le_four_pow m
        have h2 : m+m = 2*m := by ring
        rw [h2] at hle hc
        calc Lc (2*m) ≤ Lc m * Nat.choose (2*m) m := hle
          _ ≤ 4^m * 4^m := Nat.mul_le_mul (ih m (by omega)) hc
          _ = 4^(2*m) := by ring
      · have hd := Lc_dvd m (m+1) (by omega)
        have hle := Nat.le_of_dvd (mul_pos (Nat.pos_of_ne_zero (Lc_ne_zero (m+1)))
          (Nat.choose_pos (by omega))) hd
        have h2 : m+1+m = 2*m+1 := by ring
        rw [h2] at hle
        calc Lc (2*m+1) ≤ Lc (m+1) * Nat.choose (2*m+1) m := hle
          _ ≤ 4^(m+1) * 4^m := Nat.mul_le_mul (ih (m+1) (by omega)) (Nat.choose_middle_le_pow m)
          _ = 4^(2*m+1) := by ring

/-- `lcm(1,…,N) = Finset lcm` form as used in `PadeArith.Lcm5`: `lcm(1..5n) ≤ 4^{5n}`. -/
theorem lcm_Icc_le_four_pow (N : ℕ) : (Finset.Icc 1 N).lcm id ≤ 4^N := Lc_le_four_pow N

/-- The T1 denominator is at most `73728^n = (2^3·3^2·4^5)^n`. -/
theorem Dn_le (n : ℕ) : PadeArith.Dn n ≤ 73728^n := by
  unfold PadeArith.Dn
  have h : PadeArith.Lcm5 n ≤ 4^(5*n) := Lc_le_four_pow (5*n)
  have h' : (PadeArith.Lcm5 n : ℤ) ≤ 4^(5*n) := by exact_mod_cast h
  calc (2:ℤ)^(3*n) * 3^(2*n) * (PadeArith.Lcm5 n : ℤ) ≤ 2^(3*n) * 3^(2*n) * 4^(5*n) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = 73728^n := by rw [pow_mul, pow_mul, pow_mul, ← mul_pow, ← mul_pow]; norm_num

end Collatz.LcmBound

#print axioms Collatz.LcmBound.Lc_dvd
#print axioms Collatz.LcmBound.Lc_le_four_pow
#print axioms Collatz.LcmBound.Dn_le
