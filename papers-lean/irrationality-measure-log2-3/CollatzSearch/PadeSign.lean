import CollatzSearch.PadeArithQ

/-!
# Sign facts for the family `Vq_n`, `n` odd (side project, NOT Goal progress;
`no_nontrivial_cycles` remains OPEN)

For `n = 2m+1`, `Vq_n(u) = (u-1)^{4n}(2u-3)^{2n}(3u-4)^{3n}(5u-6)^{n+1}` has one factor with
odd exponent, `(3u-4)^{3n}`; the others have even exponents. Hence `Vq_n ≤ 0` for `u ≤ 4/3`
and `Vq_n ≥ 0` for `u ≥ 4/3`, and with `g(u) = Vq_n(u)/u^{5n+1}`:
`E1 = ∫_1^{4/3} g ≤ 0 ≤ E2 = ∫_{4/3}^{3/2} g`. These are unconditional, and they supply
conjunct (iii) of `SignApprox` (`SignSplit.lean`) for this family. Conjuncts (i), (ii), (iv)
(explicit sup bound and lower bound for `|E1|`) are NOT formalized.
-/

open Polynomial

namespace CollatzSearch.PadeSign
open PadeArith PadeArithQ

/-- Evaluation of `Vq_n` over ℝ as the product of powers of linear factors. -/
theorem Vq_eval_eq (n : ℕ) (u : ℝ) : ((Vq n).map (Int.castRingHom ℝ)).eval u =
    (u-1)^(4*n) * (2*u-3)^(2*n) * (3*u-4)^(3*n) * (5*u-6)^(n+1) := by
  simp [Vq, Vp]; ring

/-- For `n = 2m+1`: `Vq_n(u)` = (a product of squares) · `(3u-4)^{3n}`. -/
theorem Vq_odd_eval (m : ℕ) (u : ℝ) : ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u =
    (((u-1)^(2*(2*m+1)))^2 * ((2*u-3)^(2*m+1))^2 * ((5*u-6)^(m+1))^2) *
      (3*u-4)^(3*(2*m+1)) := by
  rw [Vq_eval_eq]; ring

/-- For odd `n` and `1 ≤ u ≤ 4/3`: `Vq_n(u) ≤ 0`. -/
theorem Vq_odd_nonpos (m : ℕ) (u : ℝ) (_h1 : 1 ≤ u) (h2 : u ≤ 4/3) :
    ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u ≤ 0 := by
  rw [Vq_odd_eval]
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  exact (Odd.pow_nonpos_iff ⟨3*m+1, by ring⟩).mpr (by linarith)

/-- For odd `n` and `u ≥ 4/3`: `Vq_n(u) ≥ 0`. -/
theorem Vq_odd_nonneg (m : ℕ) (u : ℝ) (h1 : 4/3 ≤ u) :
    0 ≤ ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u := by
  rw [Vq_odd_eval]
  exact mul_nonneg (by positivity) (pow_nonneg (by linarith) _)

/-- For odd `n`: `∫_1^{4/3} Vq_n(u)/u^{5n+1} du ≤ 0` (conjunct (iii), first half). -/
theorem E1_nonpos (m : ℕ) :
    ∫ u in (1:ℝ)..(4/3), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u / u^(5*(2*m+1)+1)
      ≤ 0 := by
  have h : 0 ≤ ∫ u in (1:ℝ)..(4/3),
      -(((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u / u^(5*(2*m+1)+1)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    have hu0 : (0:ℝ) < u := by linarith [hu.1]
    rw [neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (Vq_odd_nonpos m u hu.1 hu.2) (by positivity)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- For odd `n`: `∫_{4/3}^{3/2} Vq_n(u)/u^{5n+1} du ≥ 0` (conjunct (iii), second half). -/
theorem E2_nonneg (m : ℕ) :
    0 ≤ ∫ u in (4/3:ℝ)..(3/2), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u /
      u^(5*(2*m+1)+1) := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  have hu0 : (0:ℝ) < u := by linarith [hu.1]
  exact div_nonneg (Vq_odd_nonneg m u hu.1) (by positivity)

end CollatzSearch.PadeSign

#print axioms CollatzSearch.PadeSign.Vq_eval_eq
#print axioms CollatzSearch.PadeSign.Vq_odd_nonpos
#print axioms CollatzSearch.PadeSign.Vq_odd_nonneg
#print axioms CollatzSearch.PadeSign.E1_nonpos
#print axioms CollatzSearch.PadeSign.E2_nonneg
