import NormBig
import NormCycleAll

/-!
# mixed up/down pairs at `r ≥ 40901` (DIRECTIVES 2(b))

Setting as in `NormMixed`: `gcd(A, r) = 1`, `3^r + 1 < 2^A`, `q = 2^A - 3^r`, `g ∈ ZMod q` with
`g^r = 2`, `g^A = 3`, `θ = 2^{1/r}`; up flip at `k` (partial sum `+1`), down flip at `k'`
(partial sum `-1`), `ρ = kA mod r`, `ρ' = k'A mod r`.

* `mixed_rel`: the relation `2 + (g-1)(2g^{r-1-ρ} - g^{r-1-ρ'}) = 0` from `q ∣ B(v)` (factored
  out of `NormMixed.no_cycle_mixed_flips`).
* `rev_engine`: filtered Hadamard engine for `1 - g - 2g^d + 2g^{d+1} + g^s = 0`
  (`E = 4+t+t² + (16+4t+4t²)Z + (4+t)Y`, `Q = 1+t+4(1+t)Z+Y`).
* `no_cycle_mixed_flips_rev` (T2): the reversed order `2 ≤ ρ`, `ρ + 3 ≤ ρ' ≤ r - 3`, region
  `5·4^{(ρ'+1)/r} + 24·4^{(ρ'-ρ)/r} ≤ 29.8`, word level, `r ≥ 40901`. The margin (`F ≤ 8.9507`)
  only exists because of `NormBig.size_contra_big` (threshold `8.96` instead of `8.76`).
* `no_cycle_mixed_flips_big` (T3): `NormCycleAll`'s order `ρ' < ρ` with the region bound `28.9 → 29.8`.
* `cycle_mixed_flips_rev`, `cycle_mixed_flips_big`: cycle forms (`m ≠ 1`; `r ≥ 40901` from
  `NormCycleAll.cycle_params`).

**Scope.** For a *valid* word (all letters `≥ 1`) with `r < A < 2r`,
an up flip needs `ρ ≥ r - a` and a down flip needs `ρ' < a`, where `a = A - r`
(`NormCycleAll.up_site_of_valid` / `down_site_of_valid`). So a valid pair with `ρ < ρ'` has
`r - a ≤ ρ < ρ' < a`, while the T2 region forces `ρ' ≤ 0.107 r`; hence T2 applies to valid
words only when `a ≥ 0.893 r`, i.e. `A ≥ 1.893 r`. For an actual cycle with minimum `> 1`,
`2^L / 3^r = ∏(1 + 1/(3n_i)) ≤ (10/9)^r < 2^{0.16 r}` (all odd `n_i ≥ 3`), so `L < 1.75 r`;
with the known minimum bounds `L < 1.6 r`, and the cycle
form `cycle_mixed_flips_rev` is (provably by elementary means, though not formalised here)
**vacuous**. More strongly, for a valid pair with `ρ < ρ'` and `A ≤ 1.6 r`, `s = ρ'+1 > 0.4 r`
gives `E/4 ≥ 1.5 + 1.25·4^{0.4} + 6 > 9.6`, beyond any size threshold `< 9`: this engine cannot
handle cycle-relevant reversed pairs at all. T2 is therefore a word-level statement (relevant
to words with `A ≥ 1.893 r`, e.g. letters in `{1,2}` close to all-2, or `A > 2r` words, whose
flips are always valid). T3's region does meet cycle-relevant valid words (`ρ` near `r`, `ρ'`
small).

Credit: Knight, Lebel, Mghirbi, Solomon (norm framework). Word level,
-/

namespace Collatz.NormMixedRev
open Collatz.NormGoal Collatz.NormReduce Collatz.NormSparse
  Collatz.NormTwo Collatz.NormFilter Collatz.NormFlips
  Collatz.NormMixed Collatz.NormBig Finset

/-! ### The common relation for a mixed pair -/

/-- **Mixed-pair relation.** If the partial sums of `v` are those of `chr r A` plus one at `k`
and minus one at `k'`, and `q = 2^A - 3^r` divides `B(v)`, then in `ZMod q`, with `g^r = 2`,
`2 + (g-1)(2 g^{r-1-ρ} - g^{r-1-ρ'}) = 0` (`ρ = kA mod r`, `ρ' = k'A mod r`). This is the
first step of `NormMixed.no_cycle_mixed_flips`, independent of the order of `ρ, ρ'`. -/
theorem mixed_rel (r A : ℕ) (hr2 : 2 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k')
    (v : ℕ → ℕ) (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0))
    (hdiv : (2 ^ A - 3 ^ r) ∣ Bnum r v) :
    ∃ g : ZMod (2 ^ A - 3 ^ r), g ^ r = 2 ∧ IsUnit (2 : ZMod (2 ^ A - 3 ^ r)) ∧
      2 + (g - 1) * (2 * g ^ (r - 1 - k * A % r) - g ^ (r - 1 - k' * A % r)) = 0 := by
  obtain ⟨g, h2, h3⟩ := exists_g (by omega) hcop hq
  have hAr := r_lt_A hq
  have hA1 : 1 ≤ A := by omega
  have hK := knight_identity hr2 hcop hq h2 h3
  set G := g ^ ((A - 1) * (r - 1)) with hG
  have hgu := isUnit_g (by omega) hq h2
  have hGu : IsUnit G := hgu.pow _
  have h2u : IsUnit (2 : ZMod (2 ^ A - 3 ^ r)) := h2 ▸ hgu.pow r
  have hBv : (Bnum r v : ZMod (2 ^ A - 3 ^ r)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hBw := cast_Bnum (R := ZMod (2 ^ A - 3 ^ r)) r (NormGoal.chr r A)
  set Fw : ℕ → ZMod (2 ^ A - 3 ^ r) :=
    fun i => 3 ^ (r - 1 - i) * 2 ^ psum (NormGoal.chr r A) i with hFw
  have hpt : ∀ i ∈ range r, 2 * ((3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum v i) =
      2 * Fw i + ((if i = k then 2 * Fw i else 0) - (if i = k' then Fw i else 0)) := by
    intro i hi
    have hvi := hv i (mem_range.mp hi)
    by_cases e1 : i = k
    · have e2 : ¬ i = k' := by omega
      rw [if_pos e1, if_neg e2] at hvi
      have hp : psum v i = psum (NormGoal.chr r A) i + 1 := by omega
      simp only [hFw]; rw [hp, if_pos e1, if_neg e2, pow_succ]; ring
    · by_cases e2 : i = k'
      · rw [if_neg e1, if_pos e2] at hvi
        have hp : psum (NormGoal.chr r A) i = psum v i + 1 := by omega
        simp only [hFw]; rw [hp, if_neg e1, if_pos e2, pow_succ]; ring
      · rw [if_neg e1, if_neg e2] at hvi
        have hp : psum v i = psum (NormGoal.chr r A) i := by omega
        simp only [hFw]; rw [hp, if_neg e1, if_neg e2]; ring
  have hsum : 2 * (Bnum r v : ZMod (2 ^ A - 3 ^ r)) =
      2 * (Bnum r (NormGoal.chr r A) : ZMod (2 ^ A - 3 ^ r)) + (2 * Fw k - Fw k') := by
    rw [cast_Bnum, mul_sum, sum_congr rfl hpt, sum_add_distrib, sum_sub_distrib, sum_ite_eq',
      sum_ite_eq', if_pos (mem_range.mpr hk.2), if_pos (mem_range.mpr hk'.2), hBw, mul_sum]
  have hF : ∀ j, j < r → Fw j = G * g ^ (r - 1 - j * A % r) :=
    fun j hj => term_chr h2 h3 hA1 hj
  rw [hBv, hF k hk.2, hF k' hk'.2] at hsum
  have heq : 2 * G + (g - 1) * (2 * (G * g ^ (r - 1 - k * A % r)) -
      G * g ^ (r - 1 - k' * A % r)) = 0 := by
    linear_combination -2 * hK - (g - 1) * hsum
  exact ⟨g, h2, h2u, hGu.mul_right_eq_zero.mp (by linear_combination heq)⟩

/-! ### The reversed order `ρ < ρ'`: a coefficient-2 pentanomial -/

/-- Coefficients of `1 - z - 2z^d + 2z^{d+1} + z^s`. -/
def cR (d s n : ℕ) : ℤ := ind 0 n - ind 1 n - 2 * ind d n + 2 * ind (d + 1) n + ind s n

/-- Coefficients of the filtered sequence `2c_n + c_{n-1}` (no wrap). -/
def eR (d s n : ℕ) : ℤ :=
  2 * ind 0 n - ind 1 n - ind 2 n - 4 * ind d n + 2 * ind (d + 1) n + 2 * ind (d + 2) n +
    2 * ind s n + ind (s + 1) n

theorem cR_zero {d s : ℕ} (hd : 3 ≤ d) (hds : d + 3 ≤ s) : cR d s 0 = 1 := by
  have h1 : (0:ℕ) ≠ d := by omega
  have h2 : (0:ℕ) ≠ d + 1 := by omega
  have h3 : (0:ℕ) ≠ s := by omega
  simp [cR, ind, h1, h3]

theorem efil_cR {r d s : ℕ} (hd : 3 ≤ d) (hds : d + 3 ≤ s) (hsr : s + 2 ≤ r) {n : ℕ} :
    efil r (cR d s) n = eR d s n := by
  unfold efil
  split_ifs with h0
  · subst h0; unfold cR eR ind; split_ifs <;> first | omega | contradiction
  · have h1 : 1 ≤ n := by omega
    unfold cR eR
    rw [ind_pred h1, ind_pred h1, ind_pred h1, ind_pred h1, ind_pred h1]
    have : ind 0 n = 0 := by unfold ind; split_ifs <;> omega
    rw [this]; ring

theorem eR_sq {d s : ℕ} (hd : 3 ≤ d) (hds : d + 3 ≤ s) (n : ℕ) :
    (eR d s n) ^ 2 = 4 * ind 0 n + ind 1 n + ind 2 n + 16 * ind d n + 4 * ind (d + 1) n +
      4 * ind (d + 2) n + 4 * ind s n + ind (s + 1) n := by
  unfold eR ind; split_ifs <;> omega

theorem cR_sq {d s : ℕ} (hd : 3 ≤ d) (hds : d + 3 ≤ s) (n : ℕ) :
    (cR d s n) ^ 2 = ind 0 n + ind 1 n + 4 * ind d n + 4 * ind (d + 1) n + ind s n := by
  unfold cR ind; split_ifs <;> omega

theorem rel_cR {q r d s : ℕ} (hd : 3 ≤ d) (hds : d + 3 ≤ s) (hsr : s + 2 ≤ r) (g : ZMod q) :
    ∑ n ∈ range r, ((cR d s n : ℤ) : ZMod q) * g ^ n =
      1 - g - 2 * g ^ d + 2 * g ^ (d + 1) + g ^ s := by
  unfold cR; push_cast
  simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum]
  rw [sum_ind_g (by omega), sum_ind_g (by omega), sum_ind_g (by omega), sum_ind_g (by omega),
    sum_ind_g (by omega)]
  simp

theorem sum_eR {r d s : ℕ} (hd : 3 ≤ d) (hds : d + 3 ≤ s) (hsr : s + 2 ≤ r) (θ : ℝ) :
    ∑ n ∈ range r, ((eR d s n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      4 + θ ^ 2 + (θ ^ 2) ^ 2 + (16 + 4 * θ ^ 2 + 4 * (θ ^ 2) ^ 2) * θ ^ (2 * d) +
        (4 + θ ^ 2) * θ ^ (2 * s) := by
  have hpt : ∀ n, ((eR d s n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      4 * (((ind 0 n : ℤ) : ℝ) * θ ^ (2 * n)) + ((ind 1 n : ℤ) : ℝ) * θ ^ (2 * n) +
      ((ind 2 n : ℤ) : ℝ) * θ ^ (2 * n) + 16 * (((ind d n : ℤ) : ℝ) * θ ^ (2 * n)) +
      4 * (((ind (d + 1) n : ℤ) : ℝ) * θ ^ (2 * n)) +
      4 * (((ind (d + 2) n : ℤ) : ℝ) * θ ^ (2 * n)) +
      4 * (((ind s n : ℤ) : ℝ) * θ ^ (2 * n)) + ((ind (s + 1) n : ℤ) : ℝ) * θ ^ (2 * n) := by
    intro n
    have h := congrArg (fun z : ℤ => (z : ℝ)) (eR_sq hd hds n)
    push_cast at h
    rw [h]; ring
  rw [sum_congr rfl fun n _ => hpt n]
  simp only [sum_add_distrib, ← mul_sum]
  rw [sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega),
    sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega)]
  have e1 : θ ^ (2 * (s + 1)) = θ ^ 2 * θ ^ (2 * s) := by rw [← pow_add]; congr 1; ring
  have e2 : θ ^ (2 * (d + 1)) = θ ^ 2 * θ ^ (2 * d) := by rw [← pow_add]; congr 1; ring
  have e3 : θ ^ (2 * (d + 2)) = (θ ^ 2) ^ 2 * θ ^ (2 * d) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [e1, e2, e3]; ring

theorem sum_cR {r d s : ℕ} (hd : 3 ≤ d) (hds : d + 3 ≤ s) (hsr : s + 2 ≤ r) (θ : ℝ) :
    ∑ n ∈ range r, ((cR d s n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      1 + θ ^ 2 + 4 * (1 + θ ^ 2) * θ ^ (2 * d) + θ ^ (2 * s) := by
  have hpt : ∀ n, ((cR d s n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      ((ind 0 n : ℤ) : ℝ) * θ ^ (2 * n) + ((ind 1 n : ℤ) : ℝ) * θ ^ (2 * n) +
      4 * (((ind d n : ℤ) : ℝ) * θ ^ (2 * n)) + 4 * (((ind (d + 1) n : ℤ) : ℝ) * θ ^ (2 * n)) +
      ((ind s n : ℤ) : ℝ) * θ ^ (2 * n) := by
    intro n
    have h := congrArg (fun z : ℤ => (z : ℝ)) (cR_sq hd hds n)
    push_cast at h
    rw [h]; ring
  rw [sum_congr rfl fun n _ => hpt n]
  simp only [sum_add_distrib, ← mul_sum]
  rw [sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega),
    sum_ind_θ (by omega)]
  have e2 : θ ^ (2 * (d + 1)) = θ ^ 2 * θ ^ (2 * d) := by rw [← pow_add]; congr 1; ring
  rw [e2]; ring

/-- **Reversed mixed engine.** The relation `1 - g - 2g^d + 2g^{d+1} + g^s = 0`
(`3 ≤ d`, `d + 3 ≤ s ≤ r - 2`) gives the filtered Hadamard bound `q^2 ≤ (E/4 + Q/r)^r` with
`E = 4+t+t² + (16+4t+4t²)Z + (4+t)Y`, `Q = 1+t+4(1+t)Z+Y` (`t = θ²`, `Z = θ^{2d}`,
`Y = θ^{2s}`). -/
theorem rev_engine {q r d s : ℕ} (hq1 : 1 < q) (hd : 3 ≤ d) (hds : d + 3 ≤ s) (hsr : s + 2 ≤ r)
    (g : ZMod q) (hg : g ^ r = 2) (h : 1 - g - 2 * g ^ d + 2 * g ^ (d + 1) + g ^ s = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 ≤ ((4 + θ ^ 2 + (θ ^ 2) ^ 2 + (16 + 4 * θ ^ 2 + 4 * (θ ^ 2) ^ 2) * θ ^ (2 * d) +
        (4 + θ ^ 2) * θ ^ (2 * s)) / 4 +
        (1 + θ ^ 2 + 4 * (1 + θ ^ 2) * θ ^ (2 * d) + θ ^ (2 * s)) / r) ^ r := by
  have hc0 : Odd (cR d s 0) := by rw [cR_zero hd hds]; decide
  have hrel : ∑ n ∈ range r, ((cR d s n : ℤ) : ZMod q) * g ^ n = 0 := by
    rw [rel_cR hd hds hsr g, h]
  have H := filter_engine' hq1 (by omega) (cR d s) hc0 g hg hrel θ hθ hθr
  have hE : ∑ n ∈ range r, ((efil r (cR d s) n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      ∑ n ∈ range r, ((eR d s n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) :=
    sum_congr rfl fun n _ => by rw [efil_cR hd hds hsr]
  rwa [hE, sum_eR hd hds hsr, sum_cR hd hds hsr] at H

/-- Size finish for the reversed engine at `r ≥ 40901` (`F ≤ 8.9507 < 8.96`). -/
theorem finish_rev {r A : ℕ} {θ : ℝ} (hr : 40901 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hAr : r ≤ A)
    (hθ : 0 < θ) (hθr : θ ^ r = 2) {Y Z : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z)
    (hYZ : 5 * Y + 24 * Z ≤ 149 / 5)
    (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤ ((4 + θ ^ 2 + (θ ^ 2) ^ 2 +
        (16 + 4 * θ ^ 2 + 4 * (θ ^ 2) ^ 2) * Z + (4 + θ ^ 2) * Y) / 4 +
        (1 + θ ^ 2 + 4 * (1 + θ ^ 2) * Z + Y) / r) ^ r) :
    False := by
  have hr0 : 0 < r := by omega
  have ht := t_le_big hr hθ hθr
  have ht1 : (1:ℝ) ≤ θ ^ 2 := one_le_pow₀ (theta_ge_one hr0 hθ hθr)
  set t := θ ^ 2 with htdef
  have htt : t ^ 2 ≤ (1 + 3 / 40901) ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
  have htY : t * Y ≤ (1 + 3 / 40901) * Y := mul_le_mul_of_nonneg_right ht (by linarith)
  have htZ : t * Z ≤ (1 + 3 / 40901) * Z := mul_le_mul_of_nonneg_right ht (by linarith)
  have httZ : t ^ 2 * Z ≤ (1 + 3 / 40901) ^ 2 * Z := mul_le_mul_of_nonneg_right htt (by linarith)
  have hE : (4 + t + t ^ 2 + (16 + 4 * t + 4 * t ^ 2) * Z + (4 + t) * Y) / 4 ≤ 89504 / 10000 := by
    nlinarith
  have hr' : (40901:ℝ) ≤ r := by exact_mod_cast hr
  have hD : (1 + t + 4 * (1 + t) * Z + Y) / r ≤ 3 / 10000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 + t + 4 * (1 + t) * Z + Y ≤ 12 := by nlinarith
    nlinarith
  have hF0 : 0 ≤ (4 + t + t ^ 2 + (16 + 4 * t + 4 * t ^ 2) * Z + (4 + t) * Y) / 4 +
      (1 + t + 4 * (1 + t) * Z + Y) / r := by positivity
  refine size_contra_big hr hq hAr hθ hθr hF0 hQ (fun _ => by linarith) (fun hi => ?_)
  have := X_ge hr0 hθ hθr hAr hi
  linarith

/-- Size finish for the `NormCycleAll` engine at `r ≥ 40901` with the wider region `5Y + 6X ≤ 29.8`. -/
theorem finish_mixed_big {r A : ℕ} {θ : ℝ} (hr : 40901 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A)
    (hAr : r ≤ A) (hθ : 0 < θ) (hθr : θ ^ r = 2) {Y X : ℝ} (hY : 1 ≤ Y) (hX : 1 ≤ X)
    (hYX : 5 * Y + 6 * X ≤ 149 / 5)
    (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤ ((4 + θ ^ 2 + (θ ^ 2) ^ 2 + (4 + θ ^ 2) * Y +
        (4 + θ ^ 2 + (θ ^ 2) ^ 2) * X) / 4 + (1 + θ ^ 2 + Y + (1 + θ ^ 2) * X) / r) ^ r) :
    False := by
  have hr0 : 0 < r := by omega
  have ht := t_le_big hr hθ hθr
  have ht1 : (1:ℝ) ≤ θ ^ 2 := one_le_pow₀ (theta_ge_one hr0 hθ hθr)
  set t := θ ^ 2 with htdef
  have htt : t ^ 2 ≤ (1 + 3 / 40901) ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
  have htY : t * Y ≤ (1 + 3 / 40901) * Y := mul_le_mul_of_nonneg_right ht (by linarith)
  have htX : t * X ≤ (1 + 3 / 40901) * X := mul_le_mul_of_nonneg_right ht (by linarith)
  have httX : t ^ 2 * X ≤ (1 + 3 / 40901) ^ 2 * X := mul_le_mul_of_nonneg_right htt (by linarith)
  have hE : (4 + t + t ^ 2 + (4 + t) * Y + (4 + t + t ^ 2) * X) / 4 ≤ 89504 / 10000 := by
    nlinarith
  have hr' : (40901:ℝ) ≤ r := by exact_mod_cast hr
  have hD : (1 + t + Y + (1 + t) * X) / r ≤ 4 / 10000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 + t + Y + (1 + t) * X ≤ 16 := by nlinarith
    nlinarith
  have hF0 : 0 ≤ (4 + t + t ^ 2 + (4 + t) * Y + (4 + t + t ^ 2) * X) / 4 +
      (1 + t + Y + (1 + t) * X) / r := by positivity
  refine size_contra_big hr hq hAr hθ hθr hF0 hQ (fun _ => by linarith) (fun hi => ?_)
  have := X_ge hr0 hθ hθr hAr hi
  linarith

/-- **Mixed up/down flips in the reversed order `ρ < ρ'` (coprime).** Let
`r ≥ 40901`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`. Let `k ≠ k'` be sites in `(0, r)` with
`ρ = kA mod r`, `ρ' = k'A mod r` satisfying `2 ≤ ρ`, `ρ + 3 ≤ ρ'`, `ρ' + 3 ≤ r` and
`5·4^{(ρ'+1)/r} + 24·4^{(ρ'-ρ)/r} ≤ 29.8`. If the partial sums of `v` equal those of the
Christoffel word `chr r A` plus one at `k` (up flip) and minus one at `k'` (down flip),
agreeing elsewhere below `r`, then `(2^A - 3^r) ∤ B(v)`.
Proof: the mixed relation `2 + 2(g-1)g^p - (g-1)g^{p'} = 0` (`p = r-1-ρ > p' = r-1-ρ'`) times
`g^{r-p'}/2` is `1 - g - 2g^d + 2g^{d+1} + g^s = 0` (`d = ρ'-ρ`, `s = ρ'+1`; the up term wraps
past `g^r = 2`), and the filtered Hadamard engine gives `q^2 ≤ F^r` with `F ≤ 8.9507`, which
`NormBig.size_contra_big` (threshold `8.96`, `r ≥ 40901`) excludes.
Scope: for valid words with `A < 2r` this region needs `A ≥ 1.893 r` (see the module doc);
it is a word-level result. -/
theorem no_cycle_mixed_flips_rev (r A : ℕ) (hr : 40901 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (H1 : 2 ≤ k * A % r) (H2 : k * A % r + 3 ≤ k' * A % r)
    (H3 : k' * A % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * A % r + 1 : ℕ) : ℝ) / r) +
      24 * (4:ℝ) ^ (((k' * A % r - k * A % r : ℕ) : ℝ) / r) ≤ 149 / 5)
    (v : ℕ → ℕ) (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  have hnt := nontrivial_q hq
  have hr0 : 0 < r := by omega
  have hAr := r_lt_A hq
  obtain ⟨g, h2, h2u, hR⟩ := mixed_rel r A (by omega) hcop hq k k' hk hk' hne v hv hdiv
  set ρ := k * A % r with hρ
  set ρ' := k' * A % r with hρ'
  set s := ρ' + 1 with hs
  set d := ρ' - ρ with hd
  have hgs1 : g ^ (r - 1 - ρ') * g ^ s = 2 := by
    rw [← pow_add, show r - 1 - ρ' + s = r by omega, h2]
  have hgs2 : g ^ (r - 1 - ρ) * g ^ s = 2 * g ^ d := by
    rw [← pow_add, show r - 1 - ρ + s = r + d by omega, pow_add, h2]
  have hR' : 2 * (1 - g - 2 * g ^ d + 2 * g ^ (d + 1) + g ^ s) = 0 := by
    linear_combination g ^ s * hR - 2 * (g - 1) * hgs2 + (g - 1) * hgs1
  have hrel : 1 - g - 2 * g ^ d + 2 * g ^ (d + 1) + g ^ s = 0 := h2u.mul_right_eq_zero.mp hR'
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  set θ : ℝ := (2:ℝ) ^ ((r:ℝ)⁻¹) with hθdef
  have hθ : 0 < θ := by positivity
  have hθr : θ ^ r = 2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
  have hE := rev_engine hq1 (show 3 ≤ d by omega) (show d + 3 ≤ s by omega)
    (show s + 2 ≤ r by omega) g h2 hrel θ hθ hθr
  have hY : θ ^ (2 * s) = (4:ℝ) ^ (((k' * A % r + 1 : ℕ) : ℝ) / r) := theta_pow_eq hr0
  have hZ : θ ^ (2 * d) = (4:ℝ) ^ (((k' * A % r - k * A % r : ℕ) : ℝ) / r) := theta_pow_eq hr0
  have hθ1 := theta_ge_one hr0 hθ hθr
  have hY1 : (1:ℝ) ≤ θ ^ (2 * s) := one_le_pow₀ hθ1
  have hZ1 : (1:ℝ) ≤ θ ^ (2 * d) := one_le_pow₀ hθ1
  exact finish_rev hr hq hAr.le hθ hθr hY1 hZ1 (by rw [hY, hZ]; exact H4) hE

/-- **`NormCycleAll`'s mixed pair (`ρ' < ρ`) with a wider region at `r ≥ 40901`.** As
`NormMixed.no_cycle_mixed_flips`, with `r ≥ 40901` and the region bound `28.9` raised to
`29.8`: `5·4^{(ρ'+1)/r} + 6·4^{(r-ρ+ρ')/r} ≤ 29.8`. -/
theorem no_cycle_mixed_flips_big (r A : ℕ) (hr : 40901 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (H1 : 2 ≤ k' * A % r) (H2 : k' * A % r + 3 ≤ k * A % r)
    (H3 : k * A % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * A % r + 1 : ℕ) : ℝ) / r) +
      6 * (4:ℝ) ^ (((r - k * A % r + k' * A % r : ℕ) : ℝ) / r) ≤ 149 / 5)
    (v : ℕ → ℕ) (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  have hnt := nontrivial_q hq
  have hr0 : 0 < r := by omega
  have hAr := r_lt_A hq
  obtain ⟨g, h2, h2u, hR⟩ := mixed_rel r A (by omega) hcop hq k k' hk hk' hne v hv hdiv
  set ρ := k * A % r with hρ
  set ρ' := k' * A % r with hρ'
  set s := ρ' + 1 with hs
  set m := r - ρ + ρ' with hm
  have hgs1 : g ^ (r - 1 - ρ') * g ^ s = 2 := by
    rw [← pow_add, show r - 1 - ρ' + s = r by omega, h2]
  have hgs2 : g ^ (r - 1 - ρ) * g ^ s = g ^ m := by
    rw [← pow_add]; congr 1; omega
  have hR' : 2 * (1 - g + g ^ s - g ^ m + g ^ (m + 1)) = 0 := by
    linear_combination g ^ s * hR - 2 * (g - 1) * hgs2 + (g - 1) * hgs1
  have hrel : 1 - g + g ^ s - g ^ m + g ^ (m + 1) = 0 := h2u.mul_right_eq_zero.mp hR'
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  set θ : ℝ := (2:ℝ) ^ ((r:ℝ)⁻¹) with hθdef
  have hθ : 0 < θ := by positivity
  have hθr : θ ^ r = 2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
  have hE := mixed_engine hq1 (show 3 ≤ s by omega) (show s + 2 ≤ m by omega)
    (show m + 3 ≤ r by omega) g h2 hrel θ hθ hθr
  have hY : θ ^ (2 * s) = (4:ℝ) ^ (((k' * A % r + 1 : ℕ) : ℝ) / r) := theta_pow_eq hr0
  have hX : θ ^ (2 * m) = (4:ℝ) ^ (((r - k * A % r + k' * A % r : ℕ) : ℝ) / r) := theta_pow_eq hr0
  have hθ1 := theta_ge_one hr0 hθ hθr
  have hY1 : (1:ℝ) ≤ θ ^ (2 * s) := one_le_pow₀ hθ1
  have hX1 : (1:ℝ) ≤ θ ^ (2 * m) := one_le_pow₀ hθ1
  exact finish_mixed_big hr hq hAr.le hθ hθr hY1 hX1 (by rw [hY, hX]; exact H4) hE

section Cycle
open CollatzProof Collatz.NormCycleAll

/-- **Cycle form of `no_cycle_mixed_flips_rev`.** No positive `T`-cycle through `m ≠ 1`
(period `L`, `r` odd steps, `gcd(L, r) = 1`) has a valuation word whose partial sums are those
of `chr r L` plus one at `k` and minus one at `k'`, with `ρ = kL mod r < ρ' = k'L mod r` in the
region `2 ≤ ρ`, `ρ + 3 ≤ ρ' ≤ r - 3`, `5·4^{(ρ'+1)/r} + 24·4^{(ρ'-ρ)/r} ≤ 29.8`. (`r ≥ 40901`
comes from `NormCycleAll.cycle_params`.) **CYCLE-VACUOUS (formally proved in `NormGeom`):**
`NormGeom.cycle_mixed_flips_rev_vacuous` shows that these hypotheses (even without
`gcd(L, r) = 1`) are never satisfied by an actual cycle: validity forces `ρ ≥ r - (L - r)` and
`ρ' < L - r`, and `200L < 317r` (`NormGeom.cycle_ratio`) then contradicts the region bound.
Stated for completeness only. -/
theorem cycle_mixed_flips_rev {m L r : ℕ} {v : ℕ → ℕ} (hcop : Nat.Coprime L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (H1 : 2 ≤ k * L % r) (H2 : k * L % r + 3 ≤ k' * L % r)
    (H3 : k' * L % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * L % r + 1 : ℕ) : ℝ) / r) +
      24 * (4:ℝ) ^ (((k' * L % r - k * L % r : ℕ) : ℝ) / r) ≤ 149 / 5)
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r L) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) : False := by
  obtain ⟨_, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨hq, hdiv⟩ := cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_mixed_flips_rev r L hrb hcop hq k k' hk hk' hne H1 H2 H3 H4 v hv hdiv

/-- **Cycle form of `no_cycle_mixed_flips_big`** (`ρ' < ρ`, region bound `29.8`). -/
theorem cycle_mixed_flips_big {m L r : ℕ} {v : ℕ → ℕ} (hcop : Nat.Coprime L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (H1 : 2 ≤ k' * L % r) (H2 : k' * L % r + 3 ≤ k * L % r)
    (H3 : k * L % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * L % r + 1 : ℕ) : ℝ) / r) +
      6 * (4:ℝ) ^ (((r - k * L % r + k' * L % r : ℕ) : ℝ) / r) ≤ 149 / 5)
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r L) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) : False := by
  obtain ⟨_, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨hq, hdiv⟩ := cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_mixed_flips_big r L hrb hcop hq k k' hk hk' hne H1 H2 H3 H4 v hv hdiv

end Cycle

end Collatz.NormMixedRev

#print axioms Collatz.NormMixedRev.mixed_rel
#print axioms Collatz.NormMixedRev.rev_engine
#print axioms Collatz.NormMixedRev.finish_rev
#print axioms Collatz.NormMixedRev.finish_mixed_big
#print axioms Collatz.NormMixedRev.no_cycle_mixed_flips_rev
#print axioms Collatz.NormMixedRev.no_cycle_mixed_flips_big
#print axioms Collatz.NormMixedRev.cycle_mixed_flips_rev
#print axioms Collatz.NormMixedRev.cycle_mixed_flips_big
