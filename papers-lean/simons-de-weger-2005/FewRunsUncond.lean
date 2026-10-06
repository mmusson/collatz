import SignSplit
import PadeLower
import PadeSup

/-!
# Conjunct (ii) of `SignApprox`, the witness `signApprox_Vq`, and the
unconditional "≤ 2 odd runs ⇒ trivial" theorem for `T`-cycles.
-/

namespace Collatz
open PadeArith PadeArithQ PadeSign PadeAssembly PadeLower PadeSup

/-- `D'_n ≤ 24·73728^n` (from `lcm(1..N) ≤ 4^N`). -/
theorem Dq_le_int (n : ℕ) : Dq n ≤ 24 * 73728^n := by
  have hL : (Lcm5q n : ℤ) ≤ 4^(5*n+1) := by exact_mod_cast LcmBound.Lc_le_four_pow (5*n+1)
  calc Dq n ≤ 2^(3*n+1) * 3^(2*n+1) * 4^(5*n+1) := by
        unfold Dq; exact mul_le_mul_of_nonneg_left hL (by positivity)
    _ = 24 * 73728^n := by
        rw [show (73728:ℤ) = 2^3*3^2*4^5 by norm_num]
        simp only [mul_pow, pow_mul, pow_succ]; ring

/-- `D'_n ≤ 24·73728^n` (real cast). -/
theorem Dq_le (n : ℕ) : (Dq n : ℝ) ≤ 24 * 73728^n := by
  exact_mod_cast Dq_le_int n

/-- Floor-factor absorption: with `σ = 73728/97000`, `σ^{2m+1} · 2^{⌊m/2⌋} ≤ 1`. -/
theorem sigma_floor (m : ℕ) : (73728/97000:ℝ)^(2*m+1) * 2^(m/2) ≤ 1 := by
  set σ : ℝ := 73728/97000 with hσ
  have h0 : 0 ≤ σ := by norm_num [hσ]
  have h1 : σ ≤ 1 := by norm_num [hσ]
  have hs0 : 0 ≤ σ^2 := by positivity
  have hs1 : σ^2 ≤ 1 := pow_le_one₀ h0 h1
  have hq : 2*(m/2) ≤ m := Nat.mul_div_le m 2
  have a1 : σ^(2*m+1) ≤ (σ^2)^m := by
    rw [← pow_mul]; exact pow_le_pow_of_le_one h0 h1 (by omega)
  have a2 : (σ^2)^m ≤ ((σ^2)^2)^(m/2) := by
    calc (σ^2)^m ≤ (σ^2)^(2*(m/2)) := pow_le_pow_of_le_one hs0 hs1 hq
      _ = ((σ^2)^2)^(m/2) := pow_mul _ _ _
  have a3 : ((σ^2)^2)^(m/2) * 2^(m/2) ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ (by positivity); norm_num [hσ]
  calc σ^(2*m+1) * 2^(m/2) ≤ ((σ^2)^2)^(m/2) * 2^(m/2) :=
        mul_le_mul_of_nonneg_right (a1.trans a2) (by positivity)
    _ ≤ 1 := a3

/-- Conjunct (ii), first form: `|Q_n(2log2-log3) - P1_n| · 2^{⌊m/2⌋} ≤ 2^46`, `n = 2m+1`. -/
theorem form1_sup (m : ℕ) :
    |(Qn (2*m+1):ℝ) * (2*Real.log 2 - Real.log 3) - P1n (2*m+1)| * 2^(m/2) ≤ 2^46 := by
  rw [← form1_eq, abs_mul]
  have hD1 : (1:ℝ) ≤ Dq (2*m+1) := by exact_mod_cast Dq_pos (2*m+1)
  rw [abs_of_pos (by linarith)]
  have hE := E1_abs_le (2*m+1)
  have hD := Dq_le (2*m+1)
  have hS := sigma_floor m
  have e : (24 * 73728^(2*m+1) : ℝ) * ((2/3) * (1/97000:ℝ)^(2*m+1)) =
      16 * (73728/97000:ℝ)^(2*m+1) := by
    rw [div_eq_mul_one_div (73728:ℝ), mul_pow]; ring
  have h2 : (0:ℝ) ≤ 2^(m/2) := by positivity
  calc (Dq (2*m+1):ℝ) * |∫ u in (1:ℝ)..(4/3), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u /
          u^(5*(2*m+1)+1)| * 2^(m/2)
      ≤ (24 * 73728^(2*m+1) : ℝ) * ((2/3) * (1/97000:ℝ)^(2*m+1)) * 2^(m/2) := by
        apply mul_le_mul_of_nonneg_right _ h2
        exact mul_le_mul hD hE (abs_nonneg _) (by positivity)
    _ = 16 * ((73728/97000:ℝ)^(2*m+1) * 2^(m/2)) := by rw [e]; ring
    _ ≤ 16 * 1 := by gcongr
    _ ≤ 2^46 := by norm_num

/-- Conjunct (ii), second form: `|Q_n(2log3-3log2) - P2_n| · 2^{⌊m/2⌋} ≤ 2^46`, `n = 2m+1`. -/
theorem form2_sup (m : ℕ) :
    |(Qn (2*m+1):ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2n (2*m+1)| * 2^(m/2) ≤ 2^46 := by
  rw [← form2_eq, abs_mul]
  have hD1 : (1:ℝ) ≤ Dq (2*m+1) := by exact_mod_cast Dq_pos (2*m+1)
  rw [abs_of_pos (by linarith)]
  have hE := E2_abs_le (2*m+1)
  have hD := Dq_le (2*m+1)
  have hS := sigma_floor m
  have e : (24 * 73728^(2*m+1) : ℝ) * ((1/3) * (1/97000:ℝ)^(2*m+1)) =
      8 * (73728/97000:ℝ)^(2*m+1) := by
    rw [div_eq_mul_one_div (73728:ℝ), mul_pow]; ring
  have h2 : (0:ℝ) ≤ 2^(m/2) := by positivity
  calc (Dq (2*m+1):ℝ) * |∫ u in (4/3:ℝ)..(3/2), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u /
          u^(5*(2*m+1)+1)| * 2^(m/2)
      ≤ (24 * 73728^(2*m+1) : ℝ) * ((1/3) * (1/97000:ℝ)^(2*m+1)) * 2^(m/2) := by
        apply mul_le_mul_of_nonneg_right _ h2
        exact mul_le_mul hD hE (abs_nonneg _) (by positivity)
    _ = 8 * ((73728/97000:ℝ)^(2*m+1) * 2^(m/2)) := by rw [e]; ring
    _ ≤ 8 * 1 := by gcongr
    _ ≤ 2^46 := by norm_num

/-- **Unconditional witness** of the sign-split interface: `SignApprox 74 37 46 2` holds for
`Q_m = Qn(2m+1)`, `P1_m = P1n(2m+1)`, `P2_m = P2n(2m+1)` (the `Vq` Padé family). -/
theorem signApprox_Vq : SignApprox 74 37 46 2 (fun m => Qn (2*m+1)) (fun m => P1n (2*m+1))
    (fun m => P2n (2*m+1)) := by
  intro m
  refine ⟨Qn_abs_le_odd m, form1_sup m, form2_sup m, form1_nonpos m, form2_nonneg m, ?_⟩
  have hL := form1_lower m
  have hmono : (2:ℝ)^(26 + 37*m) ≤ 2^(46 + 37*m) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact hL.trans (mul_le_mul_of_nonneg_left hmono (abs_nonneg _))

/-- **Unconditional** (classical: Steiner 1977 / Simons 2005 re-derived): every positive `T`-cycle
with at most 2 odd runs is trivial, `z = 1 ∨ z = 2`. -/
theorem few_runs_cycle_trivial_uncond {z L : ℕ} (hz : 0 < z) (hL : 0 < L)
    (hc : CollatzProof.T^[L] z = z) (hr : oddRuns L z ≤ 2) : z = 1 ∨ z = 2 := by
  refine few_runs_cycle_trivial_of_signApprox (a := 74) (b := 37) (c := 46) (d := 2) (t := 119)
    (Q0 := 2^100) (by norm_num) signApprox_Vq (by norm_num) (by norm_num) (by norm_num [K1big])
    ?_ (by norm_num) hz hL hc hr
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

end Collatz

#print axioms Collatz.Dq_le
#print axioms Collatz.form1_sup
#print axioms Collatz.form2_sup
#print axioms Collatz.signApprox_Vq
#print axioms Collatz.few_runs_cycle_trivial_uncond
