import PadeSign

/-!
# Generic single-box sup bound for the `Vq` integrand

If `1 ≤ a` and on `[a,b]` we have `|u-1| ≤ A1`, `|2u-3| ≤ A2`, `|3u-4| ≤ A3`, `|5u-6| ≤ A4`, then
`|Vq_n(u)/u^{5n+1}| ≤ (A1^4 A2^2 A3^3 A4/a^5)^n (A4/a)` on `[a,b]` (`box_bound`), and the integral
over `[a,b]` is bounded by `(b-a)` times that (`box_integral_bound`). Preparation for conjunct (ii)
of `SignApprox`; the box instantiation (≈32 boxes on `[1,4/3]`, ≈8 on `[4/3,3/2]`) is NOT done.
-/

open Polynomial

namespace Collatz.PadeBox
open PadeArith PadeArithQ PadeSign

/-- Single-box pointwise bound on `|Vq_n(u)/u^{5n+1}|`. -/
theorem box_bound (n : ℕ) (a b A1 A2 A3 A4 : ℝ) (ha : 1 ≤ a)
    (h1 : ∀ u ∈ Set.Icc a b, |u-1| ≤ A1) (h2 : ∀ u ∈ Set.Icc a b, |2*u-3| ≤ A2)
    (h3 : ∀ u ∈ Set.Icc a b, |3*u-4| ≤ A3) (h4 : ∀ u ∈ Set.Icc a b, |5*u-6| ≤ A4)
    (u : ℝ) (hu : u ∈ Set.Icc a b) :
    |((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)| ≤
      (A1^4*A2^2*A3^3*A4/a^5)^n * (A4/a) := by
  have hu0 : 0 < u := by linarith [hu.1]
  have ha0 : 0 < a := by linarith
  rw [Vq_eval_eq, abs_div, abs_pow u, abs_of_pos hu0, abs_mul, abs_mul, abs_mul,
    abs_pow, abs_pow, abs_pow, abs_pow]
  have p1 := pow_le_pow_left₀ (abs_nonneg _) (h1 u hu) (4*n)
  have p2 := pow_le_pow_left₀ (abs_nonneg _) (h2 u hu) (2*n)
  have p3 := pow_le_pow_left₀ (abs_nonneg _) (h3 u hu) (3*n)
  have p4 := pow_le_pow_left₀ (abs_nonneg _) (h4 u hu) (n+1)
  have q1 := mul_le_mul p1 p2 (by positivity) (le_trans (by positivity) p1)
  have q2 := mul_le_mul q1 p3 (by positivity) (le_trans (by positivity) q1)
  have q3 := mul_le_mul q2 p4 (by positivity) (le_trans (by positivity) q2)
  have hU : a^(5*n+1) ≤ u^(5*n+1) := pow_le_pow_left₀ ha0.le hu.1 _
  have key := div_le_div₀ (le_trans (by positivity) q3) q3 (by positivity) hU
  refine le_trans key (le_of_eq ?_)
  have gen : ∀ x1 x2 x3 x4 y : ℝ, y ≠ 0 → x1^(4*n) * x2^(2*n) * x3^(3*n) * x4^(n+1) / y^(5*n+1) =
      (x1^4*x2^2*x3^3*x4/y^5)^n * (x4/y) := by
    intro x1 x2 x3 x4 y hy
    rw [div_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
      pow_succ x4, pow_succ y]
    field_simp
  exact gen _ _ _ _ _ ha0.ne' 

/-- Single-box bound on `|∫_a^b Vq_n(u)/u^{5n+1} du|`. -/
theorem box_integral_bound (n : ℕ) (a b A1 A2 A3 A4 : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
    (h1 : ∀ u ∈ Set.Icc a b, |u-1| ≤ A1) (h2 : ∀ u ∈ Set.Icc a b, |2*u-3| ≤ A2)
    (h3 : ∀ u ∈ Set.Icc a b, |3*u-4| ≤ A3) (h4 : ∀ u ∈ Set.Icc a b, |5*u-6| ≤ A4) :
    |∫ u in a..b, ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)| ≤
      (b-a) * ((A1^4*A2^2*A3^3*A4/a^5)^n * (A4/a)) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := (A1^4*A2^2*A3^3*A4/a^5)^n * (A4/a))
    (f := fun u => ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)) (by
      intro u hu
      rw [Set.uIoc_of_le hab] at hu
      rw [Real.norm_eq_abs]
      exact box_bound n a b A1 A2 A3 A4 ha h1 h2 h3 h4 u ⟨hu.1.le, hu.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at this
  linarith

end Collatz.PadeBox

#print axioms Collatz.PadeBox.box_bound
#print axioms Collatz.PadeBox.box_integral_bound
