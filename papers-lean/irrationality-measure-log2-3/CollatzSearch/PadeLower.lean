import CollatzSearch.PadeAssembly

/-!
# Explicit lower bound for `|E1|` (conjunct (iv) of `SignApprox`)
(side project, NOT Goal progress; `no_nontrivial_cycles` remains OPEN)

For `n = 2m+1`, `E1 = ∫_1^{4/3} Vq_n(u)/u^{5n+1} du ≤ 0`, and
`1 ≤ (-E1)·2^{26+37m}` (`negE1_lower`), because on `[11/10, 9/8]` the negated integrand is
`≥ ρ^n/3` with `ρ = (1/10)^4(3/4)^2(5/8)^3(3/8)(8/9)^5` (`log2 ρ ≈ -18.42`), and
`2^19ρ ≥ 1`, `2^37ρ^2 ≥ 1`, `2^7 ≥ 120`.
Consequently (`form1_lower`) `1 ≤ |Q_n(2log2-log3) - P1_n|·2^{26+37m}`: conjunct (iv) with
`b = 37`, `c ≥ 26`.
-/

open Polynomial

namespace CollatzSearch.PadeLower
open PadeArith PadeArithQ PadeSign PadeAssembly

/-- `ρ = (1/10)^4 (3/4)^2 (5/8)^3 (3/8) (8/9)^5`, the per-step lower rate of `-g` on `[11/10,9/8]`. -/
noncomputable def ρ : ℝ := (1/10:ℝ)^4*(3/4)^2*(5/8)^3*(3/8)*(8/9)^5

/-- For `n = 2m+1`: `-Vq_n(u) = (u-1)^{4n}(3-2u)^{2n}(4-3u)^{3n}(6-5u)^{n+1}`. -/
theorem negVq_odd_eval (m : ℕ) (u : ℝ) :
    -((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u =
      (u-1)^(4*(2*m+1)) * (3-2*u)^(2*(2*m+1)) * (4-3*u)^(3*(2*m+1)) * (6-5*u)^((2*m+1)+1) := by
  rw [Vq_eval_eq]
  have e1 : (2*u-3)^(2*(2*m+1)) = (3-2*u)^(2*(2*m+1)) := by rw [pow_mul, pow_mul]; ring
  have e2 : (5*u-6)^((2*m+1)+1) = (6-5*u)^((2*m+1)+1) := by
    rw [show (2*m+1)+1 = 2*(m+1) by ring, pow_mul, pow_mul]; ring
  have e3 : (3*u-4)^(3*(2*m+1)) = -(4-3*u)^(3*(2*m+1)) := by
    rw [show 3*(2*m+1) = 2*(3*m+1)+1 by ring, pow_succ, pow_succ, pow_mul, pow_mul]; ring
  rw [e1, e2, e3]; ring

/-- For `n = 2m+1` and `u ∈ [11/10, 9/8]`: `-Vq_n(u)/u^{5n+1} ≥ ρ^n/3`. -/
theorem neg_integrand_ge (m : ℕ) (u : ℝ) (h1 : 11/10 ≤ u) (h2 : u ≤ 9/8) :
    (1/3:ℝ) * ρ^(2*m+1) ≤ -(((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u / u^(5*(2*m+1)+1)) := by
  set n := 2*m+1 with hn
  rw [← neg_div, negVq_odd_eval]
  have hu0 : 0 < u := by linarith
  have hL : (1/10:ℝ)^(4*n) * (3/4)^(2*n) * (5/8)^(3*n) * (3/8)^(n+1) ≤
      (u-1)^(4*n) * (3-2*u)^(2*n) * (4-3*u)^(3*n) * (6-5*u)^(n+1) := by
    have a1 : (0:ℝ) ≤ 1/10 := by norm_num
    have a2 : (0:ℝ) ≤ 3/4 := by norm_num
    have a3 : (0:ℝ) ≤ 5/8 := by norm_num
    have a4 : (0:ℝ) ≤ 3/8 := by norm_num
    have b1 : (1/10:ℝ) ≤ u-1 := by linarith
    have b2 : (3/4:ℝ) ≤ 3-2*u := by linarith
    have b3 : (5/8:ℝ) ≤ 4-3*u := by linarith
    have b4 : (3/8:ℝ) ≤ 6-5*u := by linarith
    have p1 := pow_le_pow_left₀ a1 b1 (4*n)
    have p2 := pow_le_pow_left₀ a2 b2 (2*n)
    have p3 := pow_le_pow_left₀ a3 b3 (3*n)
    have p4 := pow_le_pow_left₀ a4 b4 (n+1)
    have q1 := mul_le_mul p1 p2 (by positivity) (le_trans (by positivity) p1)
    have q2 := mul_le_mul q1 p3 (by positivity) (le_trans (by positivity) q1)
    exact mul_le_mul q2 p4 (by positivity) (le_trans (by positivity) q2)
  have hU : u^(5*n+1) ≤ (9/8:ℝ)^(5*n+1) := pow_le_pow_left₀ hu0.le h2 _
  have key := div_le_div₀ (le_trans (by positivity) hL) hL (by positivity) hU
  refine le_trans (le_of_eq ?_) key
  have gen : ∀ x1 x2 x3 x4 x5 : ℝ, x1^(4*n) * x2^(2*n) * x3^(3*n) * x4^(n+1) * x5^(5*n+1) =
      (x4*x5) * (x1^4*x2^2*x3^3*x4*x5^5)^n := by intro x1 x2 x3 x4 x5; ring
  rw [show ((9:ℝ)/8)^(5*n+1) = ((8/9:ℝ)^(5*n+1))⁻¹ by rw [← inv_pow]; norm_num,
    div_inv_eq_mul, gen, ρ]
  norm_num

/-- `ρ^{2m+1}/120 · 2^{26+37m} ≥ 1` (exact rational arithmetic). -/
theorem numerics (m : ℕ) : 1 ≤ ρ^(2*m+1) / 120 * 2^(26 + 37*m) := by
  have h1 : 1 ≤ (2:ℝ)^19 * ρ := by unfold ρ; norm_num
  have h2 : 1 ≤ (2:ℝ)^37 * ρ^2 := by unfold ρ; norm_num
  have gen : ∀ r t : ℝ, r^(2*m+1) / 120 * t^(26 + 37*m) = (t^7/120) * (t^19 * r) * (t^37 * r^2)^m := by
    intro r t; ring
  rw [gen]
  have h3 : 1 ≤ ((2:ℝ)^37 * ρ^2)^m := one_le_pow₀ h2
  have h4 : (1:ℝ) ≤ 2^7/120 := by norm_num
  calc (1:ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

/-- For `n = 2m+1`: `1 ≤ (-∫_1^{4/3} Vq_n(u)/u^{5n+1} du)·2^{26+37m}`. -/
theorem negE1_lower (m : ℕ) :
    1 ≤ (-∫ u in (1:ℝ)..(4/3), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u / u^(5*(2*m+1)+1))
        * 2^(26 + 37*m) := by
  set g : ℝ → ℝ := fun u => ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u / u^(5*(2*m+1)+1)
    with hg
  have hint : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable (fun u => -g u)
      MeasureTheory.volume a b := fun a b ha hb =>
    (integrand_intervalIntegrable (2*m+1) a b ha hb).neg
  have hnn : ∀ u : ℝ, 1 ≤ u → u ≤ 4/3 → 0 ≤ -g u := by
    intro u h1 h2
    have hu0 : (0:ℝ) < u := by linarith
    rw [neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (Vq_odd_nonpos m u h1 h2) (by positivity)
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hint 1 (11/10) le_rfl (by norm_num)) (hint (11/10) (4/3) (by norm_num) (by norm_num))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hint (11/10) (9/8) (by norm_num) (by norm_num)) (hint (9/8) (4/3) (by norm_num) (by norm_num))
  have hA : 0 ≤ ∫ u in (1:ℝ)..(11/10), -g u :=
    intervalIntegral.integral_nonneg (by norm_num) fun u hu => hnn u hu.1 (by linarith [hu.2])
  have hC : 0 ≤ ∫ u in (9/8:ℝ)..(4/3), -g u :=
    intervalIntegral.integral_nonneg (by norm_num) fun u hu => hnn u (by linarith [hu.1]) hu.2
  have hB : ∫ u in (11/10:ℝ)..(9/8), (1/3:ℝ) * ρ^(2*m+1) ≤ ∫ u in (11/10:ℝ)..(9/8), -g u :=
    intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (hint _ _ (by norm_num) (by norm_num)) fun u hu => neg_integrand_ge m u hu.1 hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hB
  have htot : ρ^(2*m+1) / 120 ≤ -∫ u in (1:ℝ)..(4/3), g u := by
    rw [← intervalIntegral.integral_neg, ← hsplit1, ← hsplit2]
    linarith
  have hnum := numerics m
  have h2pos : (0:ℝ) < 2^(26 + 37*m) := by positivity
  calc (1:ℝ) ≤ ρ^(2*m+1) / 120 * 2^(26 + 37*m) := hnum
    _ ≤ _ := mul_le_mul_of_nonneg_right htot h2pos.le

/-- Conjunct (iv): `1 ≤ |Q_n(2log2-log3) - P1_n|·2^{26+37m}` for `n = 2m+1`. -/
theorem form1_lower (m : ℕ) :
    1 ≤ |(Qn (2*m+1):ℝ) * (2*Real.log 2 - Real.log 3) - P1n (2*m+1)| * 2^(26 + 37*m) := by
  rw [← form1_eq]
  have hE := E1_nonpos m
  have hD : (1:ℝ) ≤ Dq (2*m+1) := by exact_mod_cast Dq_pos (2*m+1)
  have hL := negE1_lower m
  rw [abs_mul, abs_of_pos (by linarith), abs_of_nonpos hE]
  have h2pos : (0:ℝ) < 2^(26 + 37*m) := by positivity
  calc (1:ℝ) ≤ _ := hL
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ h2pos.le
      exact le_mul_of_one_le_left (by linarith) hD

end CollatzSearch.PadeLower

#print axioms CollatzSearch.PadeLower.neg_integrand_ge
#print axioms CollatzSearch.PadeLower.negE1_lower
#print axioms CollatzSearch.PadeLower.form1_lower
