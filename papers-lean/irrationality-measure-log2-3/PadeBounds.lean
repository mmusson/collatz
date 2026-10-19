/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import PadeArith
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Coefficient bounds and the integral identity for the Padé polynomial `V_n`

In this file we bound the coefficients `w_i` of the polynomial
`V_n = (X - 1)^{4n} (2X - 3)^{2n} (3X - 4)^{3n} (5X - 6)^n` of `PadeArith`, bound its degree, and
express integrals `∫_1^s p(u)/u^{K+1} du` of integer polynomials as explicit finite sums. With
`p = V_n`, `K = 5n` and `s ∈ {3/2, 4/3}` this gives the identity
`∫_1^s V_n(u) u^{-5n-1} du = w_{5n} log s + Σ_{i ≠ 5n} w_i (s^{i-5n} - 1)/(i - 5n)`.

The coefficient bound uses coefficientwise domination `Dom`: it is multiplicative, `aX - b` is
dominated by `aX + b`, and the coefficients of a polynomial with nonnegative coefficients are at
most its value at `1`.

## Main definitions

- `Dom P P'`: `|P_i| ≤ P'_i` for every `i`.
- `Wp n`: the dominating polynomial `(X + 1)^{4n} (2X + 3)^{2n} (3X + 4)^{3n} (5X + 6)^n`.
- `Fterm i K s`: `∫_1^s u^{i-K-1} du`, i.e. `log s` if `i = K` and `(s^{i-K} - 1)/(i - K)`
  otherwise.

## Main results

- `coeff_Vp_abs_le`: `|w_i| ≤ 2^{4n} 5^{2n} 7^{3n} 11^n` for every `i`.
- `natDegree_Vp_le`: `natDegree V_n ≤ 10n`.
- `integral_zpow_sub_one`: for `s ≥ 1`, `∫_1^s u^{j-1} du` is `log s` if `j = 0` and
  `(s^j - 1)/j` otherwise.
- `integral_poly_div_pow`: for `p ∈ ℤ[X]` with `natDegree p < N` and `s ≥ 1`,
  `∫_1^s p(u)/u^{K+1} du = Σ_{i<N} p_i F(i, K, s)`.

## References

- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
  Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
- M. Hata, *Rational approximations to π and some other numbers*, Acta Arith. 63 (1993), 335–349.
-/

open Polynomial

namespace Collatz.PadeArith

/-! ### Coefficientwise domination -/

/-- `P'` dominates `P` coefficientwise in absolute value. -/
def Dom (P P' : ℤ[X]) : Prop := ∀ i, |P.coeff i| ≤ P'.coeff i

theorem Dom.nonneg {P P' : ℤ[X]} (h : Dom P P') (i : ℕ) : 0 ≤ P'.coeff i :=
  le_trans (abs_nonneg _) (h i)

theorem Dom.mul {P P' R R' : ℤ[X]} (hP : Dom P P') (hR : Dom R R') : Dom (P*R) (P'*R') := by
  intro k
  rw [coeff_mul, coeff_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hP _) (hR _) (abs_nonneg _) (hP.nonneg _)

theorem dom_one : Dom 1 1 := fun i => by
  rw [coeff_one]; split_ifs <;> simp

theorem Dom.pow {P P' : ℤ[X]} (h : Dom P P') (k : ℕ) : Dom (P^k) (P'^k) := by
  induction k with
  | zero => simpa using dom_one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem dom_linear (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Dom (C a * X - C b) (C a * X + C b) := by
  intro i
  rw [coeff_linear, coeff_add, coeff_C_mul_X, coeff_C]
  rcases i with _ | _ | i <;> simp [abs_of_nonneg ha, abs_of_nonneg hb]

theorem coeff_le_eval_one {W : ℤ[X]} (h : ∀ i, 0 ≤ W.coeff i) (i : ℕ) : W.coeff i ≤ W.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hi : i < W.natDegree + 1
  · exact Finset.single_le_sum (fun j _ => h j) (Finset.mem_range.mpr hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Finset.sum_nonneg fun j _ => h j

/-! ### Size of the coefficients of `V_n` -/

/-- Dominating polynomial `W_n = (X+1)^{4n}(2X+3)^{2n}(3X+4)^{3n}(5X+6)^n`. -/
noncomputable def Wp (n : ℕ) : ℤ[X] :=
  (C 1 * X + C 1)^(4*n) * (C 2 * X + C 3)^(2*n) * (C 3 * X + C 4)^(3*n) * (C 5 * X + C 6)^n

theorem dom_Vp (n : ℕ) : Dom (Vp n) (Wp n) := by
  unfold Vp Wp
  rw [X_sub_C_eq]
  exact ((((dom_linear 1 1 (by norm_num) (by norm_num)).pow _).mul
    ((dom_linear 2 3 (by norm_num) (by norm_num)).pow _)).mul
    ((dom_linear 3 4 (by norm_num) (by norm_num)).pow _)).mul
    ((dom_linear 5 6 (by norm_num) (by norm_num)).pow _)

theorem eval_one_Wp (n : ℕ) : (Wp n).eval 1 = 2^(4*n) * 5^(2*n) * 7^(3*n) * 11^n := by
  unfold Wp; simp

/-- Coefficient bound: `|w_i| ≤ 2^{4n} 5^{2n} 7^{3n} 11^n` for every coefficient of `V_n`. -/
theorem coeff_Vp_abs_le (n i : ℕ) : |(Vp n).coeff i| ≤ 2^(4*n) * 5^(2*n) * 7^(3*n) * 11^n := by
  rw [← eval_one_Wp]
  exact le_trans (dom_Vp n i) (coeff_le_eval_one (dom_Vp n).nonneg i)

theorem natDegree_linear_le' (a b : ℤ) : (C a * X - C b).natDegree ≤ 1 :=
  by
  rw [sub_eq_add_neg, ← C_neg]; exact natDegree_linear_le

/-- `natDegree V_n ≤ 10 n`. -/
theorem natDegree_Vp_le (n : ℕ) : (Vp n).natDegree ≤ 10*n := by
  unfold Vp
  rw [X_sub_C_eq]
  have h : ∀ (a b : ℤ) (k : ℕ), ((C a * X - C b)^k).natDegree ≤ k := fun a b k =>
    le_trans natDegree_pow_le (by simpa using Nat.mul_le_mul_left k (natDegree_linear_le' a b))
  have h1 := h 1 1 (4*n)
  have h2 := h 2 3 (2*n)
  have h3 := h 3 4 (3*n)
  have h4 := h 5 6 n
  have m1 := (natDegree_mul_le (p := (C (1:ℤ) * X - C 1)^(4*n)) (q := (C (2:ℤ) * X - C 3)^(2*n)))
  have m2 := (natDegree_mul_le (p := (C 1 * X - C 1)^(4*n) * (C 2 * X - C 3)^(2*n))
    (q := (C (3:ℤ) * X - C 4)^(3*n)))
  have m3 := (natDegree_mul_le (p := (C (1:ℤ) * X - C 1)^(4*n) * (C (2:ℤ) * X - C 3)^(2*n) *
    (C (3:ℤ) * X - C 4)^(3*n)) (q := (C (5:ℤ) * X - C 6)^n))
  omega

/-! ### The integral identity -/

/-- For `s ≥ 1`, `∫_1^s u^{j-1} du` is `log s` if `j = 0` and `(s^j - 1)/j` otherwise. -/
theorem integral_zpow_sub_one (s : ℝ) (hs : 1 ≤ s) (j : ℤ) :
    ∫ u in (1:ℝ)..s, u ^ (j - 1) = if j = 0 then Real.log s else (s ^ j - 1) / j := by
  split_ifs with hj
  · subst hj
    have : ∀ u : ℝ, u ^ ((0:ℤ) - 1) = u⁻¹ := fun u => by simp
    simp_rw [this]
    rw [integral_inv_of_pos one_pos (by linarith), div_one]
  · have h0 : (0:ℝ) ∉ Set.uIcc 1 s := by
      rw [Set.uIcc_of_le hs]; intro h; linarith [h.1]
    rw [integral_zpow (Or.inr ⟨by omega, h0⟩)]
    simp

/-- `F(i,K,s) = ∫_1^s u^{i-K-1} du`: `log s` if `i = K`, else `(s^{i-K}-1)/(i-K)`. -/
noncomputable def Fterm (i K : ℕ) (s : ℝ) : ℝ :=
  if i = K then Real.log s else (s ^ ((i:ℤ) - K) - 1) / ((i:ℝ) - K)

theorem integral_zpow_Fterm (i K : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    ∫ u in (1:ℝ)..s, u ^ (((i:ℤ) - K) - 1) = Fterm i K s := by
  rw [integral_zpow_sub_one s hs, Fterm]
  by_cases h : i = K
  · subst h; simp
  · have : ((i:ℤ) - K) ≠ 0 := by omega
    simp only [this, h, ↓reduceIte]; push_cast; rfl

/-- For `p ∈ ℤ[X]` with `natDegree p < N` and `s ≥ 1`,
`∫_1^s p(u)/u^{K+1} du = Σ_{i<N} p_i · Fterm i K s`. -/
theorem integral_poly_div_pow (p : Polynomial ℤ) (N K : ℕ) (hN : p.natDegree < N) (s : ℝ)
    (hs : 1 ≤ s) :
    ∫ u in (1:ℝ)..s, (p.map (Int.castRingHom ℝ)).eval u / u ^ (K+1) =
      ∑ i ∈ Finset.range N, ((p.coeff i : ℤ) : ℝ) * Fterm i K s := by
  have hN' : (p.map (Int.castRingHom ℝ)).natDegree < N := lt_of_le_of_lt (natDegree_map_le) hN
  have hcongr : Set.EqOn (fun u : ℝ => (p.map (Int.castRingHom ℝ)).eval u / u ^ (K+1))
      (fun u => ∑ i ∈ Finset.range N, ((p.coeff i : ℤ) : ℝ) * u ^ (((i:ℤ) - K) - 1))
      (Set.uIcc 1 s) := by
    intro u hu
    rw [Set.uIcc_of_le hs] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    simp only
    rw [eval_eq_sum_range' hN', Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, eq_intCast, mul_div_assoc]
    congr 1
    rw [show ((i:ℤ) - K) - 1 = (i:ℤ) - ((K+1 : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ hu0,
      zpow_natCast, zpow_natCast]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_zpow_Fterm i K s hs]
  · intro i _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.zpow₀ continuousOn_id _ ?_
    intro u hu
    rw [Set.uIcc_of_le hs] at hu
    left; simp; linarith [hu.1]

end Collatz.PadeArith
