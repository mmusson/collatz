/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import PadeArithQ

/-!
# Signs of the integrals of `Vq_n` for odd `n`

For `n = 2m + 1`, the polynomial `Vq_n(u) = (u - 1)^{4n} (2u - 3)^{2n} (3u - 4)^{3n} (5u - 6)^{n+1}`
of `PadeArithQ` has exactly one factor with odd exponent, `(3u - 4)^{3n}`. Hence `Vq_n ≤ 0` on
`[1, 4/3]` and `Vq_n ≥ 0` on `[4/3, ∞)`, and with `g(u) = Vq_n(u)/u^{5n+1}` we get
`E1 = ∫_1^{4/3} g ≤ 0 ≤ E2 = ∫_{4/3}^{3/2} g`. This is the sign condition of the sign-split
transference in `SignSplit`.

## Main results

- `Vq_eval_eq`: evaluation of `Vq_n` over `ℝ` as a product of powers of linear factors.
- `Vq_odd_nonpos`, `Vq_odd_nonneg`: for odd `n`, `Vq_n(u) ≤ 0` on `[1, 4/3]` and `Vq_n(u) ≥ 0`
  for `u ≥ 4/3`.
- `E1_nonpos`, `E2_nonneg`: for odd `n`, `∫_1^{4/3} g ≤ 0` and `∫_{4/3}^{3/2} g ≥ 0`.

## References

- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
  Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
- M. Hata, *Rational approximations to π and some other numbers*, Acta Arith. 63 (1993), 335–349.
-/

open Polynomial

namespace Collatz.PadeSign
open PadeArith PadeArithQ

/-! ### Sign of `Vq_n` for odd `n` -/

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

/-! ### Signs of the integrals -/

/-- For odd `n`: `∫_1^{4/3} Vq_n(u)/u^{5n+1} du ≤ 0`. -/
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

/-- For odd `n`: `∫_{4/3}^{3/2} Vq_n(u)/u^{5n+1} du ≥ 0`. -/
theorem E2_nonneg (m : ℕ) :
    0 ≤ ∫ u in (4/3:ℝ)..(3/2), ((Vq (2*m+1)).map (Int.castRingHom ℝ)).eval u /
      u^(5*(2*m+1)+1) := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  have hu0 : (0:ℝ) < u := by linarith [hu.1]
  exact div_nonneg (Vq_odd_nonneg m u hu.1) (by positivity)

end Collatz.PadeSign
