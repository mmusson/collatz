import PadeSign
import LcmBound

/-!
# Assembly of the integer forms for the `Vq` Padé family

With `u_i = coeff_i(Vq_n)`, `D'_n = Dq n`, `Q_n = D'_n u_{5n}`:
* `exists_int_sum`/`S43`/`S32`: for `s ∈ {4/3, 3/2}` the rational sum
  `S_n(s) = Σ_{i<10n+2, i≠5n} D'_n u_i (s^{i-5n}-1)/(i-5n)` is an integer.
* `Dq_mul_integral_43/32`: `D'_n ∫_1^s Vq_n(u)/u^{5n+1} du = Q_n log s + S_n(s)`.
* With `P1_n = -S_n(4/3)`, `P2_n = S_n(4/3) - S_n(3/2)`:
  `form1_eq`: `D'_n E1 = Q_n (2log2 - log3) - P1_n` (`E1 = ∫_1^{4/3}`),
  `form2_eq`: `D'_n E2 = Q_n (2log3 - 3log2) - P2_n` (`E2 = ∫_{4/3}^{3/2}`).
* `Qn_abs_le`: `|Q_n| ≤ 2^{9+37n}` (conjunct (i) of `SignApprox` with `a = 74`, `c ≥ 46` for
  `n = 2m+1`, `Qn_abs_le_odd`), via `D'_n ≤ 2^{3n+1}3^{2n+1}4^{5n+1}` and
  `|u_i| ≤ 11·2^{4n}5^{2n}7^{3n}11^n`; `264·111270297600^n ≤ 2^9·(2^37)^n`.
* `form1_nonpos`, `form2_nonneg`: conjunct (iii) for `n = 2m+1`.
Conjunct (iv) is in `PadeLower.lean`; conjunct (ii) (sup bound) is NOT formalized, so no
`SignApprox` witness exists yet.
-/

open Polynomial

namespace Collatz.PadeAssembly
open PadeArith PadeArithQ PadeSign

/-- A finite sum of rationals each of which is an integer is an integer. -/
theorem exists_int_finset_sum {ι : Type*} (t : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ t, ∃ z : ℤ, f i = z) : ∃ z : ℤ, ∑ i ∈ t, f i = z := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨z1, h1⟩ := h a (Finset.mem_insert_self a t)
    obtain ⟨z2, h2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨z1 + z2, by rw [Finset.sum_insert ha, h1, h2]; push_cast; ring⟩

/-- `Q_n = D'_n · u_{5n}`, the coefficient of `log s` in `D'_n ∫_1^s Vq_n/u^{5n+1}`. -/
noncomputable def Qn (n : ℕ) : ℤ := Dq n * (Vq n).coeff (5*n)

/-- For `s ∈ {3/2, 4/3}`, `Σ_{i<10n+2, i≠5n} D'_n u_i (s^{i-5n}-1)/(i-5n)` is an integer. -/
theorem exists_int_sum (n : ℕ) (s : ℚ) (hs : s = 3/2 ∨ s = 4/3) :
    ∃ z : ℤ, (z:ℚ) = ∑ i ∈ (Finset.range (10*n+2)).erase (5*n),
      (Dq n:ℚ) * ((Vq n).coeff i:ℚ) * (s^((i:ℤ) - 5*n) - 1) / ((i:ℚ) - 5*n) := by
  obtain ⟨z, hz⟩ := exists_int_finset_sum ((Finset.range (10*n+2)).erase (5*n))
    (fun i => (Dq n:ℚ) * ((Vq n).coeff i:ℚ) * (s^((i:ℤ) - 5*n) - 1) / ((i:ℚ) - 5*n)) (by
      intro i hi
      rw [Finset.mem_erase, Finset.mem_range] at hi
      obtain ⟨z1, h1⟩ := integral_term_q n i (by omega) hi.1 s hs
      obtain ⟨z2, h2⟩ := integral_term_one_q n i (by omega) hi.1
      refine ⟨z1 - z2, ?_⟩
      push_cast
      rw [← h1, ← h2]; ring)
  exact ⟨z, hz.symm⟩

/-- The integer `S_n(4/3)`. -/
noncomputable def S43 (n : ℕ) : ℤ := (exists_int_sum n (4/3) (Or.inr rfl)).choose
/-- The integer `S_n(3/2)`. -/
noncomputable def S32 (n : ℕ) : ℤ := (exists_int_sum n (3/2) (Or.inl rfl)).choose

theorem S43_spec (n : ℕ) : (S43 n : ℚ) = ∑ i ∈ (Finset.range (10*n+2)).erase (5*n),
      (Dq n:ℚ) * ((Vq n).coeff i:ℚ) * ((4/3:ℚ)^((i:ℤ) - 5*n) - 1) / ((i:ℚ) - 5*n) :=
  (exists_int_sum n (4/3) (Or.inr rfl)).choose_spec

theorem S32_spec (n : ℕ) : (S32 n : ℚ) = ∑ i ∈ (Finset.range (10*n+2)).erase (5*n),
      (Dq n:ℚ) * ((Vq n).coeff i:ℚ) * ((3/2:ℚ)^((i:ℤ) - 5*n) - 1) / ((i:ℚ) - 5*n) :=
  (exists_int_sum n (3/2) (Or.inl rfl)).choose_spec

/-- General identity for a rational `s ≥ 1` and an integer `z` equal to the rational sum. -/
theorem Dq_mul_integral_aux (n : ℕ) (s : ℚ) (hs : (1:ℝ) ≤ (s:ℝ)) (z : ℤ)
    (hz : (z:ℚ) = ∑ i ∈ (Finset.range (10*n+2)).erase (5*n),
      (Dq n:ℚ) * ((Vq n).coeff i:ℚ) * (s^((i:ℤ) - 5*n) - 1) / ((i:ℚ) - 5*n)) :
    (Dq n:ℝ) * ∫ u in (1:ℝ)..(s:ℝ), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)
      = (Qn n:ℝ) * Real.log (s:ℝ) + (z:ℝ) := by
  have hdeg : (Vq n).natDegree < 10*n+2 := by have := natDegree_Vq_le n; omega
  rw [integral_poly_div_pow (Vq n) (10*n+2) (5*n) hdeg (s:ℝ) hs]
  have hmem : 5*n ∈ Finset.range (10*n+2) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hmem, mul_add]
  have hz' : (z:ℝ) = ((z:ℚ):ℝ) := by push_cast; rfl
  rw [hz', hz]
  push_cast
  congr 1
  · simp only [Fterm, Qn, ↓reduceIte]; push_cast; ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ 5*n := (Finset.mem_erase.mp hi).1
    simp only [Fterm, hne, ↓reduceIte]
    push_cast
    ring

/-- `D'_n ∫_1^{4/3} Vq_n(u)/u^{5n+1} du = Q_n log(4/3) + S_n(4/3)`. -/
theorem Dq_mul_integral_43 (n : ℕ) :
    (Dq n:ℝ) * ∫ u in (1:ℝ)..(4/3), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)
      = (Qn n:ℝ) * Real.log (4/3) + (S43 n:ℝ) := by
  have := Dq_mul_integral_aux n (4/3) (by norm_num) (S43 n) (S43_spec n)
  push_cast at this; exact this

/-- `D'_n ∫_1^{3/2} Vq_n(u)/u^{5n+1} du = Q_n log(3/2) + S_n(3/2)`. -/
theorem Dq_mul_integral_32 (n : ℕ) :
    (Dq n:ℝ) * ∫ u in (1:ℝ)..(3/2), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)
      = (Qn n:ℝ) * Real.log (3/2) + (S32 n:ℝ) := by
  have := Dq_mul_integral_aux n (3/2) (by norm_num) (S32 n) (S32_spec n)
  push_cast at this; exact this


/-- `P1_n = -S_n(4/3)`. -/
noncomputable def P1n (n : ℕ) : ℤ := -S43 n
/-- `P2_n = S_n(4/3) - S_n(3/2)`. -/
noncomputable def P2n (n : ℕ) : ℤ := S43 n - S32 n

theorem log_43 : Real.log (4/3) = 2*Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  push_cast; ring

theorem log_32 : Real.log (3/2) = Real.log 3 - Real.log 2 :=
  Real.log_div (by norm_num) (by norm_num)

/-- `D'_n · E1 = Q_n (2log2 - log3) - P1_n`, `E1 = ∫_1^{4/3} Vq_n(u)/u^{5n+1} du`. -/
theorem form1_eq (n : ℕ) :
    (Dq n:ℝ) * ∫ u in (1:ℝ)..(4/3), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)
      = (Qn n:ℝ) * (2*Real.log 2 - Real.log 3) - P1n n := by
  rw [Dq_mul_integral_43, log_43, P1n]; push_cast; ring

/-- `Vq_n(u)/u^{5n+1}` is interval integrable on any interval inside `[1,∞)`. -/
theorem integrand_intervalIntegrable (n : ℕ) (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun u : ℝ => ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1))
      MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (Polynomial.continuous _).continuousOn
    (continuous_pow _).continuousOn ?_
  intro u hu
  have : 1 ≤ u := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hu; linarith [hu.1]
    · rw [Set.uIcc_of_ge h] at hu; linarith [hu.1]
  positivity

/-- `D'_n · E2 = Q_n (2log3 - 3log2) - P2_n`, `E2 = ∫_{4/3}^{3/2} Vq_n(u)/u^{5n+1} du`. -/
theorem form2_eq (n : ℕ) :
    (Dq n:ℝ) * ∫ u in (4/3:ℝ)..(3/2), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)
      = (Qn n:ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2n n := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (integrand_intervalIntegrable n 1 (4/3) le_rfl (by norm_num))
    (integrand_intervalIntegrable n (4/3) (3/2) (by norm_num) (by norm_num))
  have e : ∫ u in (4/3:ℝ)..(3/2), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1) =
      (∫ u in (1:ℝ)..(3/2), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)) -
      ∫ u in (1:ℝ)..(4/3), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1) := by
    rw [← hadd]; ring
  rw [e, mul_sub, Dq_mul_integral_43, Dq_mul_integral_32, log_43, log_32, P2n]
  push_cast; ring

theorem Lcm5q_pos (n : ℕ) : 0 < Lcm5q n :=
  Nat.pos_of_ne_zero (LcmBound.Lc_ne_zero (5*n+1))

/-- `D'_n ≥ 1`. -/
theorem Dq_pos (n : ℕ) : (1:ℤ) ≤ Dq n := by
  unfold Dq
  have h := Lcm5q_pos n
  have : (1:ℤ) ≤ (Lcm5q n : ℤ) := by exact_mod_cast h
  have h2 : (1:ℤ) ≤ 2^(3*n+1) * 3^(2*n+1) := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  nlinarith

/-- `|Q_n| ≤ 2^{9+37n}` (in ℤ). -/
theorem Qn_abs_le_int (n : ℕ) : |Qn n| ≤ 2^(9 + 37*n) := by
  have hL : (Lcm5q n : ℤ) ≤ 4^(5*n+1) := by exact_mod_cast LcmBound.Lc_le_four_pow (5*n+1)
  have hD : |Dq n| ≤ 2^(3*n+1) * 3^(2*n+1) * 4^(5*n+1) := by
    rw [abs_of_pos (by linarith [Dq_pos n])]; unfold Dq
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  have hu := coeff_Vq_abs_le n (5*n)
  unfold Qn; rw [abs_mul]
  calc |Dq n| * |(Vq n).coeff (5*n)|
      ≤ (2^(3*n+1) * 3^(2*n+1) * 4^(5*n+1)) * (11 * (2^(4*n) * 5^(2*n) * 7^(3*n) * 11^n)) :=
        mul_le_mul hD hu (abs_nonneg _) (by positivity)
    _ = 264 * 111270297600^n := by
        rw [show (111270297600:ℤ) = 2^3*3^2*4^5*2^4*5^2*7^3*11 by norm_num]
        simp only [mul_pow, pow_mul, pow_succ]; ring
    _ ≤ 2^9 * (2^37)^n := mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
          (by positivity) (by norm_num)
    _ = 2^(9 + 37*n) := by rw [pow_add, pow_mul]

/-- `|Q_n| ≤ 2^{9+37n}` (conjunct (i)). -/
theorem Qn_abs_le (n : ℕ) : |(Qn n:ℝ)| ≤ 2^(9 + 37*n) := by
  have := Qn_abs_le_int n
  exact_mod_cast this

/-- `|Q_{2m+1}| ≤ 2^{46+74m}`. -/
theorem Qn_abs_le_odd (m : ℕ) : |(Qn (2*m+1):ℝ)| ≤ 2^(46 + 74*m) := by
  have := Qn_abs_le (2*m+1)
  rwa [show 9 + 37*(2*m+1) = 46 + 74*m by ring] at this

/-- Conjunct (iii), first half: `Q(2log2-log3) - P1 ≤ 0` for `n = 2m+1`. -/
theorem form1_nonpos (m : ℕ) :
    (Qn (2*m+1):ℝ) * (2*Real.log 2 - Real.log 3) - P1n (2*m+1) ≤ 0 := by
  rw [← form1_eq]
  have hD : (0:ℝ) ≤ Dq (2*m+1) := by exact_mod_cast (by linarith [Dq_pos (2*m+1)] : (0:ℤ) ≤ _)
  exact mul_nonpos_of_nonneg_of_nonpos hD (E1_nonpos m)

/-- Conjunct (iii), second half: `0 ≤ Q(2log3-3log2) - P2` for `n = 2m+1`. -/
theorem form2_nonneg (m : ℕ) :
    0 ≤ (Qn (2*m+1):ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2n (2*m+1) := by
  rw [← form2_eq]
  have hD : (0:ℝ) ≤ Dq (2*m+1) := by exact_mod_cast (by linarith [Dq_pos (2*m+1)] : (0:ℤ) ≤ _)
  exact mul_nonneg hD (E2_nonneg m)

end Collatz.PadeAssembly


#print axioms Collatz.PadeAssembly.exists_int_sum
#print axioms Collatz.PadeAssembly.Dq_mul_integral_43
#print axioms Collatz.PadeAssembly.Dq_mul_integral_32
#print axioms Collatz.PadeAssembly.form1_eq
#print axioms Collatz.PadeAssembly.form2_eq
#print axioms Collatz.PadeAssembly.Qn_abs_le
#print axioms Collatz.PadeAssembly.Qn_abs_le_odd
#print axioms Collatz.PadeAssembly.form1_nonpos
#print axioms Collatz.PadeAssembly.form2_nonneg
