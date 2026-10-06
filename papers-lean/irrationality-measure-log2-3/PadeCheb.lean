import FewRunsUncond
import LcmCheb
import SignSplitR
import IrrMeasure

/-!
# The `V_q` Padé family under the Chebyshev lcm bound ⇒ `IrrMeasHyp 59 (2^167)`
(known mathematics, re-derived and formalized; literature: Rhin 1987 irrationality measure ≈ 8.616
for `log 3/log 2` (from memory, unverified; non-explicit threshold); Wu–Wang 2014 ≈ 5.125
(unverified; that bound is for `log 3`))

* `Dq_le_cheb_int`: `2^{5n+1} D'_n ≤ 2^38 · 21 · 1210104^n` (from `Lc_le_cheb`).
* `Qn_abs_le_cheb`: `|Q_n| ≤ 2^{45+36n}`, so `|Q_{2m+1}| ≤ 2^{81+72m}`.
* `sigma_cheb`: `σ^{2m+1} 2^{⌊5m/2⌋} ≤ 1` for `σ = 1210104/3104000` (`32σ^4 < 1`).
* `form1_sup_cheb`, `form2_sup_cheb`: `|E_j| 2^{⌊5m/2⌋} ≤ 2^41`.
* `signApproxR_Vq : SignApproxR 72 37 81 41 26 5 2`.
* `irrMeasHyp_59 : IrrMeasHyp 59 (2^167)`; `linFormHyp_58 : LinFormHyp (2^167) 2 58`.
-/

namespace Collatz
open PadeArith PadeArithQ PadeSign PadeAssembly PadeLower PadeSup

/-- `2^{5n+1} D'_n ≤ 2^38 · 21 · 1210104^n` (Chebyshev bound at `N = 5n+1`). -/
theorem Dq_le_cheb_int (n : ℕ) : 2^(5*n+1) * Dq n ≤ 2^38 * 21 * 1210104^n := by
  have hL : ((2^(5*n+1) * LcmBound.Lc (5*n+1) : ℕ) : ℤ) ≤ ((2^37 * 7^(5*n+1) : ℕ) : ℤ) := by
    exact_mod_cast LcmCheb.Lc_le_cheb (5*n+1)
  push_cast at hL
  have hLc : (Lcm5q n : ℤ) = (LcmBound.Lc (5*n+1) : ℤ) := rfl
  unfold Dq
  rw [hLc]
  calc (2:ℤ)^(5*n+1) * (2^(3*n+1) * 3^(2*n+1) * (LcmBound.Lc (5*n+1) : ℤ))
      = 2^(3*n+1) * 3^(2*n+1) * (2^(5*n+1) * (LcmBound.Lc (5*n+1) : ℤ)) := by ring
    _ ≤ 2^(3*n+1) * 3^(2*n+1) * (2^37 * 7^(5*n+1)) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = 2^38 * 21 * 1210104^n := by
        rw [show (1210104:ℤ) = 2^3*3^2*7^5 by norm_num]
        simp only [mul_pow, pow_mul, pow_succ]; ring

/-- Real form: `D'_n ≤ 2^37 · 21 · (1210104/32)^n`. -/
theorem Dq_le_cheb (n : ℕ) : (Dq n : ℝ) ≤ 2^37 * 21 * (1210104/32:ℝ)^n := by
  have h : ((2^(5*n+1) * Dq n : ℤ) : ℝ) ≤ ((2^38 * 21 * 1210104^n : ℤ) : ℝ) := by
    exact_mod_cast Dq_le_cheb_int n
  push_cast at h
  have e : (2:ℝ)^(5*n+1) = 2 * 32^n := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [e] at h
  rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith

/-- `|Q_n| ≤ 2^{45+36n}` (in ℤ), using `1210104 · 1509200 ≤ 2^41`. -/
theorem Qn_abs_le_cheb_int (n : ℕ) : |Qn n| ≤ 2^(45 + 36*n) := by
  have hD := Dq_le_cheb_int n
  have hD0 : 0 ≤ Dq n := by linarith [Dq_pos n]
  have hu := coeff_Vq_abs_le n (5*n)
  have hu' : |(Vq n).coeff (5*n)| ≤ 11 * 1509200^n := by
    refine le_trans hu (le_of_eq ?_)
    rw [show (1509200:ℤ) = 2^4*5^2*7^3*11 by norm_num]
    simp only [mul_pow, pow_mul]
  have key : 2^(5*n+1) * |Qn n| ≤ 2^(5*n+1) * 2^(45 + 36*n) := by
    unfold Qn
    rw [abs_mul, abs_of_nonneg hD0]
    calc (2:ℤ)^(5*n+1) * (Dq n * |(Vq n).coeff (5*n)|)
        = (2^(5*n+1) * Dq n) * |(Vq n).coeff (5*n)| := by ring
      _ ≤ (2^38 * 21 * 1210104^n) * (11 * 1509200^n) :=
          mul_le_mul hD hu' (abs_nonneg _) (by positivity)
      _ = 2^38 * 231 * (1210104 * 1509200)^n := by rw [mul_pow]; ring
      _ ≤ 2^38 * 2^8 * (2^41)^n := by
          apply mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
            (by positivity) (by positivity)
      _ = 2^(5*n+1) * 2^(45 + 36*n) := by
          rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  exact le_of_mul_le_mul_left key (by positivity)

/-- `|Q_{2m+1}| ≤ 2^{81+72m}` (real cast). -/
theorem Qn_abs_le_cheb_odd (m : ℕ) : |(Qn (2*m+1):ℝ)| ≤ 2^(81 + 72*m) := by
  have := Qn_abs_le_cheb_int (2*m+1)
  rw [show 45 + 36*(2*m+1) = 81 + 72*m by ring] at this
  exact_mod_cast this

/-- With `σ = 1210104/3104000`: `σ^{2m+1} · 2^{⌊5m/2⌋} ≤ 1` (since `32σ^4 ≤ 1`). -/
theorem sigma_cheb (m : ℕ) : (1210104/3104000:ℝ)^(2*m+1) * 2^((5*m)/2) ≤ 1 := by
  set σ : ℝ := 1210104/3104000 with hσ
  have h0 : 0 ≤ σ := by norm_num [hσ]
  have h1 : σ ≤ 1 := by norm_num [hσ]
  have hk : 2*((5*m)/2) ≤ 5*m := Nat.mul_div_le _ _
  have a1 : σ^(2*m+1) ≤ σ^(2*m) := pow_le_pow_of_le_one h0 h1 (by omega)
  set x : ℝ := σ^(2*m) * 2^((5*m)/2) with hx
  have hx0 : 0 ≤ x := by positivity
  have hsq : x^2 ≤ 1 := by
    have e : x^2 = (σ^4)^m * 2^(2*((5*m)/2)) := by
      rw [hx, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
    rw [e]
    calc (σ^4)^m * 2^(2*((5*m)/2)) ≤ (σ^4)^m * 2^(5*m) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hk) (by positivity)
      _ = (σ^4 * 32)^m := by rw [mul_pow, pow_mul]; norm_num
      _ ≤ 1 := pow_le_one₀ (by positivity) (by norm_num [hσ])
  have hx1 : x ≤ 1 := by nlinarith
  calc σ^(2*m+1) * 2^((5*m)/2) ≤ σ^(2*m) * 2^((5*m)/2) :=
        mul_le_mul_of_nonneg_right a1 (by positivity)
    _ ≤ 1 := hx1

/-- Decay of the first form: `|Q_n(2log2−log3) − P1_n| · 2^{⌊5m/2⌋} ≤ 2^41`, `n = 2m+1`. -/
theorem form1_sup_cheb (m : ℕ) :
    |(Qn (2*m+1):ℝ) * (2*Real.log 2 - Real.log 3) - P1n (2*m+1)| * 2^((5*m)/2) ≤ 2^41 := by
  rw [← form1_eq, abs_mul]
  have hD1 : (1:ℝ) ≤ Dq (2*m+1) := by exact_mod_cast Dq_pos (2*m+1)
  rw [abs_of_pos (by linarith)]
  have hE := E1_abs_le (2*m+1)
  have hD := Dq_le_cheb (2*m+1)
  have hS := sigma_cheb m
  have e : (2^37 * 21 * (1210104/32:ℝ)^(2*m+1)) * ((2/3) * (1/97000:ℝ)^(2*m+1)) =
      2^37 * 14 * (1210104/3104000:ℝ)^(2*m+1) := by
    rw [show (1210104/3104000:ℝ) = (1210104/32) * (1/97000) by norm_num, mul_pow]; ring
  have h2 : (0:ℝ) ≤ 2^((5*m)/2) := by positivity
  calc (Dq (2*m+1):ℝ) * |∫ u in (1:ℝ)..(4/3), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u /
          u^(5*(2*m+1)+1)| * 2^((5*m)/2)
      ≤ (2^37 * 21 * (1210104/32:ℝ)^(2*m+1)) * ((2/3) * (1/97000:ℝ)^(2*m+1)) *
          2^((5*m)/2) := by
        apply mul_le_mul_of_nonneg_right _ h2
        exact mul_le_mul hD hE (abs_nonneg _) (by positivity)
    _ = 2^37 * 14 * ((1210104/3104000:ℝ)^(2*m+1) * 2^((5*m)/2)) := by rw [e]; ring
    _ ≤ 2^37 * 14 * 1 := by gcongr
    _ ≤ 2^41 := by norm_num

/-- Decay of the second form: `|Q_n(2log3−3log2) − P2_n| · 2^{⌊5m/2⌋} ≤ 2^41`, `n = 2m+1`. -/
theorem form2_sup_cheb (m : ℕ) :
    |(Qn (2*m+1):ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2n (2*m+1)| * 2^((5*m)/2) ≤ 2^41 := by
  rw [← form2_eq, abs_mul]
  have hD1 : (1:ℝ) ≤ Dq (2*m+1) := by exact_mod_cast Dq_pos (2*m+1)
  rw [abs_of_pos (by linarith)]
  have hE := E2_abs_le (2*m+1)
  have hD := Dq_le_cheb (2*m+1)
  have hS := sigma_cheb m
  have e : (2^37 * 21 * (1210104/32:ℝ)^(2*m+1)) * ((1/3) * (1/97000:ℝ)^(2*m+1)) =
      2^37 * 7 * (1210104/3104000:ℝ)^(2*m+1) := by
    rw [show (1210104/3104000:ℝ) = (1210104/32) * (1/97000) by norm_num, mul_pow]; ring
  have h2 : (0:ℝ) ≤ 2^((5*m)/2) := by positivity
  calc (Dq (2*m+1):ℝ) * |∫ u in (4/3:ℝ)..(3/2), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u /
          u^(5*(2*m+1)+1)| * 2^((5*m)/2)
      ≤ (2^37 * 21 * (1210104/32:ℝ)^(2*m+1)) * ((1/3) * (1/97000:ℝ)^(2*m+1)) *
          2^((5*m)/2) := by
        apply mul_le_mul_of_nonneg_right _ h2
        exact mul_le_mul hD hE (abs_nonneg _) (by positivity)
    _ = 2^37 * 7 * ((1210104/3104000:ℝ)^(2*m+1) * 2^((5*m)/2)) := by rw [e]; ring
    _ ≤ 2^37 * 7 * 1 := by gcongr
    _ ≤ 2^41 := by norm_num

/-- **Unconditional witness** of the rational-rate interface:
`SignApproxR 72 37 81 41 26 5 2` for `Q_m = Qn(2m+1)`, `P1_m = P1n(2m+1)`,
`P2_m = P2n(2m+1)` (the `V_q` Padé family with the Chebyshev lcm bound). -/
theorem signApproxR_Vq : SignApproxR 72 37 81 41 26 5 2 (fun m => Qn (2*m+1))
    (fun m => P1n (2*m+1)) (fun m => P2n (2*m+1)) := by
  intro m
  exact ⟨Qn_abs_le_cheb_odd m, form1_sup_cheb m, form2_sup_cheb m, form1_nonpos m,
    form2_nonneg m, form1_lower m⟩

/-- **Unconditional explicit irrationality measure:** `IrrMeasHyp 59 (2^167)`, i.e.
`|log₂3 − p/q| ≥ q^{−59}` for all `q ≥ 2^167` (was `IrrMeasHyp 342 (2^100)`). Known
mathematics (Rhin 1987 ≈ 8.616, unverified, non-explicit threshold; Wu–Wang 2014 ≈ 5.125,
unverified, for `log 3`); formalized here. -/
theorem irrMeasHyp_59 : IrrMeasHyp 59 (2^167) := by
  have h := irrMeasHyp_of_signApproxR (r := 44) (t := 14) (Q0 := 2^167)
    (by norm_num) (by norm_num) (by norm_num) signApproxR_Vq (by norm_num) (by norm_num)
    (by rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by norm_num))
  exact h

/-- **Unconditional** `LinFormHyp (2^167) 2 58`: `k ≥ 2^167`, `3^k < 2^L` ⇒
`2^L ≤ 4 k^58 (2^L − 3^k)` (was `LinFormHyp (2^100) 2 341`). -/
theorem linFormHyp_58 : LinFormHyp (2^167) 2 58 :=
  linFormHyp_of_irrMeas (μ := 59) (by norm_num) (by norm_num) irrMeasHyp_59

end Collatz

#print axioms Collatz.Dq_le_cheb_int
#print axioms Collatz.Qn_abs_le_cheb_int
#print axioms Collatz.sigma_cheb
#print axioms Collatz.form1_sup_cheb
#print axioms Collatz.form2_sup_cheb
#print axioms Collatz.signApproxR_Vq
#print axioms Collatz.irrMeasHyp_59
#print axioms Collatz.linFormHyp_58
