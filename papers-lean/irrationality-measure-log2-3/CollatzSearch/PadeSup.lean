import CollatzSearch.PadeBox
import CollatzSearch.PadeAssembly

/-!
# Sup bounds for `E1`, `E2` of the `Vq` Padé family
(side project, NOT Goal progress; `no_nontrivial_cycles` remains OPEN)

With `f_n(u) = Vq_n(u)/u^{5n+1}` and `R = 1/97000`:
`|∫_1^{4/3} f_n| ≤ (2/3) R^n` (`E1_abs_le`, 32 boxes of width 1/96) and
`|∫_{4/3}^{3/2} f_n| ≤ (1/3) R^n` (`E2_abs_le`, 8 boxes of width 1/48).
Each box `[a,b]` uses endpoint-max constants `A1..A4` (checked exactly: box ratio `≤ R`,
`A4/a ≤ 2`; worst box `[1+10/96, 1+11/96]`, ratio ≈ 0.9942 R).
-/

open Polynomial

namespace CollatzSearch.PadeSup
open PadeArith PadeArithQ PadeSign PadeBox PadeAssembly

/-- Box lemma with the numerics abstracted: if the box ratio is `≤ 1/97000` and `A4/a ≤ 2`, then
`|∫_a^b f_n| ≤ w · 2 · (1/97000)^n` where `w = b - a`. -/
theorem box_R (n : ℕ) (a b w A1 A2 A3 A4 : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (hw : b - a = w)
    (h1 : ∀ u ∈ Set.Icc a b, |u-1| ≤ A1) (h2 : ∀ u ∈ Set.Icc a b, |2*u-3| ≤ A2)
    (h3 : ∀ u ∈ Set.Icc a b, |3*u-4| ≤ A3) (h4 : ∀ u ∈ Set.Icc a b, |5*u-6| ≤ A4)
    (hr : A1^4*A2^2*A3^3*A4/a^5 ≤ 1/97000) (h4a : A4/a ≤ 2) :
    |∫ u in a..b, ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)| ≤
      w * (2 * (1/97000:ℝ)^n) := by
  have hmem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have e1 := le_trans (abs_nonneg _) (h1 a hmem)
  have e2 := le_trans (abs_nonneg _) (h2 a hmem)
  have e3 := le_trans (abs_nonneg _) (h3 a hmem)
  have e4 := le_trans (abs_nonneg _) (h4 a hmem)
  have ha0 : 0 < a := by linarith
  have hr0 : 0 ≤ A1^4*A2^2*A3^3*A4/a^5 := by positivity
  have hB := box_integral_bound n a b A1 A2 A3 A4 ha hab h1 h2 h3 h4
  have hp : (A1^4*A2^2*A3^3*A4/a^5)^n ≤ (1/97000:ℝ)^n := pow_le_pow_left₀ hr0 hr n
  have hq : (A1^4*A2^2*A3^3*A4/a^5)^n * (A4/a) ≤ (1/97000:ℝ)^n * 2 :=
    mul_le_mul hp h4a (by positivity) (by positivity)
  rw [hw] at hB
  have hw0 : 0 ≤ w := by rw [← hw]; linarith
  calc _ ≤ _ := hB
    _ ≤ w * ((1/97000:ℝ)^n * 2) := mul_le_mul_of_nonneg_left hq hw0
    _ = _ := by ring

local macro "bx" : tactic =>
  `(tactic| (intro u hu; obtain ⟨hu1, hu2⟩ := hu; push_cast at hu1 hu2 ⊢; rw [abs_le];
             constructor <;> linarith))

/-- The 32 boxes of `[1,4/3]`. -/
theorem grid1 (n : ℕ) : ∀ k < 32,
    |∫ u in (1 + ((k:ℕ):ℝ)/96)..(1 + ((k+1:ℕ):ℝ)/96),
        ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)| ≤ (1/96) * (2 * (1/97000:ℝ)^n) := by
  intro k hk
  interval_cases k
  · exact box_R n _ _ _ (1/96:ℝ) (1:ℝ) (1:ℝ) (1:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/48:ℝ) (47/48:ℝ) (31/32:ℝ) (91/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/32:ℝ) (23/24:ℝ) (15/16:ℝ) (43/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/24:ℝ) (15/16:ℝ) (29/32:ℝ) (27/32:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (5/96:ℝ) (11/12:ℝ) (7/8:ℝ) (19/24:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/16:ℝ) (43/48:ℝ) (27/32:ℝ) (71/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (7/96:ℝ) (7/8:ℝ) (13/16:ℝ) (11/16:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/12:ℝ) (41/48:ℝ) (25/32:ℝ) (61/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (3/32:ℝ) (5/6:ℝ) (3/4:ℝ) (7/12:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (5/48:ℝ) (13/16:ℝ) (23/32:ℝ) (17/32:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (11/96:ℝ) (19/24:ℝ) (11/16:ℝ) (23/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/8:ℝ) (37/48:ℝ) (21/32:ℝ) (41/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (13/96:ℝ) (3/4:ℝ) (5/8:ℝ) (3/8:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (7/48:ℝ) (35/48:ℝ) (19/32:ℝ) (31/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (5/32:ℝ) (17/24:ℝ) (9/16:ℝ) (13/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/6:ℝ) (11/16:ℝ) (17/32:ℝ) (7/32:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (17/96:ℝ) (2/3:ℝ) (1/2:ℝ) (1/6:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (3/16:ℝ) (31/48:ℝ) (15/32:ℝ) (11/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (19/96:ℝ) (5/8:ℝ) (7/16:ℝ) (1/16:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (5/24:ℝ) (29/48:ℝ) (13/32:ℝ) (1/24:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (7/32:ℝ) (7/12:ℝ) (3/8:ℝ) (3/32:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (11/48:ℝ) (9/16:ℝ) (11/32:ℝ) (7/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (23/96:ℝ) (13/24:ℝ) (5/16:ℝ) (19/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/4:ℝ) (25/48:ℝ) (9/32:ℝ) (1/4:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (25/96:ℝ) (1/2:ℝ) (1/4:ℝ) (29/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (13/48:ℝ) (23/48:ℝ) (7/32:ℝ) (17/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (9/32:ℝ) (11/24:ℝ) (3/16:ℝ) (13/32:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (7/24:ℝ) (7/16:ℝ) (5/32:ℝ) (11/24:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (29/96:ℝ) (5/12:ℝ) (1/8:ℝ) (49/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (5/16:ℝ) (19/48:ℝ) (3/32:ℝ) (9/16:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (31/96:ℝ) (3/8:ℝ) (1/16:ℝ) (59/96:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/3:ℝ) (17/48:ℝ) (1/32:ℝ) (2/3:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)

/-- The 8 boxes of `[4/3,3/2]`. -/
theorem grid2 (n : ℕ) : ∀ k < 8,
    |∫ u in (4/3 + ((k:ℕ):ℝ)/48)..(4/3 + ((k+1:ℕ):ℝ)/48),
        ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)| ≤ (1/48) * (2 * (1/97000:ℝ)^n) := by
  intro k hk
  interval_cases k
  · exact box_R n _ _ _ (17/48:ℝ) (1/3:ℝ) (1/16:ℝ) (37/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (3/8:ℝ) (7/24:ℝ) (1/8:ℝ) (7/8:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (19/48:ℝ) (1/4:ℝ) (3/16:ℝ) (47/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (5/12:ℝ) (5/24:ℝ) (1/4:ℝ) (13/12:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (7/16:ℝ) (1/6:ℝ) (5/16:ℝ) (19/16:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (11/24:ℝ) (1/8:ℝ) (3/8:ℝ) (31/24:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (23/48:ℝ) (1/12:ℝ) (7/16:ℝ) (67/48:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)
  · exact box_R n _ _ _ (1/2:ℝ) (1/24:ℝ) (1/2:ℝ) (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num)
      (by bx) (by bx) (by bx) (by bx) (by norm_num) (by norm_num)

/-- `|∫_1^{4/3} Vq_n(u)/u^{5n+1} du| ≤ (2/3)(1/97000)^n`. -/
theorem E1_abs_le (n : ℕ) :
    |∫ u in (1:ℝ)..(4/3), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)| ≤
      (2/3) * (1/97000:ℝ)^n := by
  set f := fun u : ℝ => ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1) with hf
  have hs := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => 1 + (k:ℝ)/96) (n := 32) (by
      intro k _
      have h0 : (0:ℝ) ≤ (k:ℝ)/96 := by positivity
      have h1 : (0:ℝ) ≤ ((k+1:ℕ):ℝ)/96 := by positivity
      exact integrand_intervalIntegrable n _ _ (by push_cast at h1 ⊢; linarith) (by push_cast at h1 ⊢; linarith))
  rw [show (1:ℝ) + ((0:ℕ):ℝ)/96 = 1 by norm_num, show (1:ℝ) + ((32:ℕ):ℝ)/96 = 4/3 by norm_num]
    at hs
  rw [← hs]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1/96:ℝ) * (2 * (1/97000:ℝ)^n))
    (fun k hk => ?_)) (le_of_eq ?_)
  · exact_mod_cast grid1 n k (Finset.mem_range.mp hk)
  · rw [Finset.sum_const, Finset.card_range]; simp only [nsmul_eq_mul]; ring

/-- `|∫_{4/3}^{3/2} Vq_n(u)/u^{5n+1} du| ≤ (1/3)(1/97000)^n`. -/
theorem E2_abs_le (n : ℕ) :
    |∫ u in (4/3:ℝ)..(3/2), ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1)| ≤
      (1/3) * (1/97000:ℝ)^n := by
  set f := fun u : ℝ => ((Vq n).map (Int.castRingHom ℝ)).eval u / u^(5*n+1) with hf
  have hs := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => 4/3 + (k:ℝ)/48) (n := 8) (by
      intro k _
      have h0 : (0:ℝ) ≤ (k:ℝ)/48 := by positivity
      have h1 : (0:ℝ) ≤ ((k+1:ℕ):ℝ)/48 := by positivity
      exact integrand_intervalIntegrable n _ _ (by push_cast at h1 ⊢; linarith) (by push_cast at h1 ⊢; linarith))
  rw [show (4/3:ℝ) + ((0:ℕ):ℝ)/48 = 4/3 by norm_num, show (4/3:ℝ) + ((8:ℕ):ℝ)/48 = 3/2 by norm_num]
    at hs
  rw [← hs]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1/48:ℝ) * (2 * (1/97000:ℝ)^n))
    (fun k hk => ?_)) (le_of_eq ?_)
  · exact_mod_cast grid2 n k (Finset.mem_range.mp hk)
  · rw [Finset.sum_const, Finset.card_range]; simp only [nsmul_eq_mul]; ring

end CollatzSearch.PadeSup

#print axioms CollatzSearch.PadeSup.box_R
#print axioms CollatzSearch.PadeSup.E1_abs_le
#print axioms CollatzSearch.PadeSup.E2_abs_le
