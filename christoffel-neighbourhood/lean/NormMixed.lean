import NormFlips

/-!
# coprime mixed up/down two-site words (DIRECTIVES 2(b))

Setting as in `NormFlips`: `r ≥ 2325`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`, `q = 2^A - 3^r`,
`g ∈ ZMod q` with `g^r = 2`, `g^A = 3`, `θ = 2^{1/r}`, `ρ_k = kA mod r`.
A *mixed pair* raises the partial sum `A_k` by one (up flip at `k`) and lowers `A_{k'}` by one
(down flip at `k'`).

* `no_cycle_mixed_flips`: in the region `2 ≤ ρ'`, `ρ' + 3 ≤ ρ ≤ r - 3`,
  `5·4^{(ρ'+1)/r} + 6·4^{(r-ρ+ρ')/r} ≤ 28.9` (e.g. `ρ' ≤ 0.2 r` and `ρ - ρ' ≥ 0.06 r`),
  `(2^A - 3^r) ∤ B(v)`. No `A < 2r` hypothesis and no entry-validity hypothesis.
* `mixed_engine`: the `NormFlips` filtered Hadamard engine applied to the pentanomial
  `1 - g + g^s - g^m + g^{m+1}` with explicit closed forms
  `E = 4+t+t²+(4+t)Y+(4+t+t²)X`, `Q = 1+t+Y+(1+t)X` (`t = θ²`, `Y = θ^{2s}`, `X = θ^{2m}`).
* `cycle_mixed_flips`: the cycle form, via `NormTwo.cycle_q`.

New ingredient: the normalisation by `g^{r-p'}` (`p' = r-1-ρ'`), which turns the relation
`2 + 2(g-1)g^p - (g-1)g^{p'} = 0` into a ±1 pentanomial with odd constant term
(`2` is a unit, `q` odd). The other region (`ρ < ρ'`) is open: the analogous normalisation
produces a coefficient-2 cluster and `E/4 ≥ 8.75` leaves no margin (consistent with the `NormTwo`
finding that adjacent opposite-sign pairs have true norm `≥ q`).

Credit: Knight, Lebel, Mghirbi, Solomon (norm framework; Mghirbi's `E ≤ 1.536 r^{2/3}` covers
small-defect words for actual cycles). Novelty only plausible for large defect area and at the
word/rational-cycle level; not a milestone.
-/

namespace CollatzSearch.NormMixed
open CollatzSearch.NormGoal CollatzSearch.NormReduce CollatzSearch.NormSparse
  CollatzSearch.NormTwo CollatzSearch.NormFilter CollatzSearch.NormFlips Finset

/-- Coefficients of `1 - z + z^s - z^m + z^{m+1}`. -/
def cM (s m n : ℕ) : ℤ := ind 0 n - ind 1 n + ind s n - ind m n + ind (m + 1) n

/-- Coefficients of `(2 + z)(1 - z + z^s - z^m + z^{m+1})` (no wrap). -/
def eM (s m n : ℕ) : ℤ :=
  2 * ind 0 n - ind 1 n - ind 2 n + 2 * ind s n + ind (s + 1) n - 2 * ind m n + ind (m + 1) n +
    ind (m + 2) n

theorem cM_zero {s m : ℕ} (hs : 3 ≤ s) (hsm : s + 2 ≤ m) : cM s m 0 = 1 := by
  unfold cM ind; split_ifs <;> omega

theorem efil_cM {r s m : ℕ} (hs : 3 ≤ s) (hsm : s + 2 ≤ m) (hmr : m + 3 ≤ r) {n : ℕ} :
    efil r (cM s m) n = eM s m n := by
  unfold efil
  split_ifs with h0
  · subst h0; unfold cM eM ind; split_ifs <;> first | omega | contradiction
  · have h1 : 1 ≤ n := by omega
    unfold cM eM
    rw [ind_pred h1, ind_pred h1, ind_pred h1, ind_pred h1, ind_pred h1]
    have : ind 0 n = 0 := by unfold ind; split_ifs <;> omega
    rw [this]; ring

theorem eM_sq {s m : ℕ} (hs : 3 ≤ s) (hsm : s + 2 ≤ m) (n : ℕ) :
    (eM s m n) ^ 2 = 4 * ind 0 n + ind 1 n + ind 2 n + 4 * ind s n + ind (s + 1) n +
      4 * ind m n + ind (m + 1) n + ind (m + 2) n := by
  unfold eM ind; split_ifs <;> omega

theorem cM_sq {s m : ℕ} (hs : 3 ≤ s) (hsm : s + 2 ≤ m) (n : ℕ) :
    (cM s m n) ^ 2 = ind 0 n + ind 1 n + ind s n + ind m n + ind (m + 1) n := by
  unfold cM ind; split_ifs <;> omega

theorem rel_cM {q r s m : ℕ} (hs : 3 ≤ s) (hsm : s + 2 ≤ m) (hmr : m + 3 ≤ r) (g : ZMod q) :
    ∑ n ∈ range r, ((cM s m n : ℤ) : ZMod q) * g ^ n = 1 - g + g ^ s - g ^ m + g ^ (m + 1) := by
  unfold cM; push_cast
  simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib]
  rw [sum_ind_g (by omega), sum_ind_g (by omega), sum_ind_g (by omega), sum_ind_g (by omega),
    sum_ind_g (by omega)]
  simp

theorem sum_eM {r s m : ℕ} (hs : 3 ≤ s) (hsm : s + 2 ≤ m) (hmr : m + 3 ≤ r) (θ : ℝ) :
    ∑ n ∈ range r, ((eM s m n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      4 + θ ^ 2 + (θ ^ 2) ^ 2 + (4 + θ ^ 2) * θ ^ (2 * s) +
        (4 + θ ^ 2 + (θ ^ 2) ^ 2) * θ ^ (2 * m) := by
  have hpt : ∀ n, ((eM s m n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      4 * (((ind 0 n : ℤ) : ℝ) * θ ^ (2 * n)) + ((ind 1 n : ℤ) : ℝ) * θ ^ (2 * n) +
      ((ind 2 n : ℤ) : ℝ) * θ ^ (2 * n) + 4 * (((ind s n : ℤ) : ℝ) * θ ^ (2 * n)) +
      ((ind (s + 1) n : ℤ) : ℝ) * θ ^ (2 * n) + 4 * (((ind m n : ℤ) : ℝ) * θ ^ (2 * n)) +
      ((ind (m + 1) n : ℤ) : ℝ) * θ ^ (2 * n) + ((ind (m + 2) n : ℤ) : ℝ) * θ ^ (2 * n) := by
    intro n
    have h := congrArg (fun z : ℤ => (z : ℝ)) (eM_sq hs hsm n)
    push_cast at h
    rw [h]; ring
  rw [sum_congr rfl fun n _ => hpt n]
  simp only [sum_add_distrib, ← mul_sum]
  rw [sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega),
    sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega)]
  have e1 : θ ^ (2 * (s + 1)) = θ ^ 2 * θ ^ (2 * s) := by rw [← pow_add]; congr 1; ring
  have e2 : θ ^ (2 * (m + 1)) = θ ^ 2 * θ ^ (2 * m) := by rw [← pow_add]; congr 1; ring
  have e3 : θ ^ (2 * (m + 2)) = (θ ^ 2) ^ 2 * θ ^ (2 * m) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [e1, e2, e3]; ring

theorem sum_cM {r s m : ℕ} (hs : 3 ≤ s) (hsm : s + 2 ≤ m) (hmr : m + 3 ≤ r) (θ : ℝ) :
    ∑ n ∈ range r, ((cM s m n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      1 + θ ^ 2 + θ ^ (2 * s) + (1 + θ ^ 2) * θ ^ (2 * m) := by
  have hpt : ∀ n, ((cM s m n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      ((ind 0 n : ℤ) : ℝ) * θ ^ (2 * n) + ((ind 1 n : ℤ) : ℝ) * θ ^ (2 * n) +
      ((ind s n : ℤ) : ℝ) * θ ^ (2 * n) + ((ind m n : ℤ) : ℝ) * θ ^ (2 * n) +
      ((ind (m + 1) n : ℤ) : ℝ) * θ ^ (2 * n) := by
    intro n
    have h := congrArg (fun z : ℤ => (z : ℝ)) (cM_sq hs hsm n)
    push_cast at h
    rw [h]; ring
  rw [sum_congr rfl fun n _ => hpt n]
  simp only [sum_add_distrib]
  rw [sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega), sum_ind_θ (by omega),
    sum_ind_θ (by omega)]
  have e2 : θ ^ (2 * (m + 1)) = θ ^ 2 * θ ^ (2 * m) := by rw [← pow_add]; congr 1; ring
  rw [e2]; ring

/-- Mixed engine: the pentanomial relation `1 - g + g^s - g^m + g^{m+1} = 0` gives the
filtered Hadamard bound with explicit closed forms. -/
theorem mixed_engine {q r s m : ℕ} (hq1 : 1 < q) (hs : 3 ≤ s) (hsm : s + 2 ≤ m) (hmr : m + 3 ≤ r)
    (g : ZMod q) (hg : g ^ r = 2) (h : 1 - g + g ^ s - g ^ m + g ^ (m + 1) = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 ≤ ((4 + θ ^ 2 + (θ ^ 2) ^ 2 + (4 + θ ^ 2) * θ ^ (2 * s) +
        (4 + θ ^ 2 + (θ ^ 2) ^ 2) * θ ^ (2 * m)) / 4 +
        (1 + θ ^ 2 + θ ^ (2 * s) + (1 + θ ^ 2) * θ ^ (2 * m)) / r) ^ r := by
  have hc0 : Odd (cM s m 0) := by rw [cM_zero hs hsm]; decide
  have hrel : ∑ n ∈ range r, ((cM s m n : ℤ) : ZMod q) * g ^ n = 0 := by
    rw [rel_cM hs hsm hmr g, h]
  have H := filter_engine' hq1 (by omega) (cM s m) hc0 g hg hrel θ hθ hθr
  have hE : ∑ n ∈ range r, ((efil r (cM s m) n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      ∑ n ∈ range r, ((eM s m n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) :=
    sum_congr rfl fun n _ => by rw [efil_cM hs hsm hmr]
  rwa [hE, sum_eM hs hsm hmr, sum_cM hs hsm hmr] at H

/-- Size finish for the mixed engine. -/
theorem finish_mixed {r A : ℕ} {θ : ℝ} (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hAr : r ≤ A)
    (hθ : 0 < θ) (hθr : θ ^ r = 2) {Y X : ℝ} (hY : 1 ≤ Y) (hX : 1 ≤ X)
    (hYX : 5 * Y + 6 * X ≤ 289 / 10)
    (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤ ((4 + θ ^ 2 + (θ ^ 2) ^ 2 + (4 + θ ^ 2) * Y +
        (4 + θ ^ 2 + (θ ^ 2) ^ 2) * X) / 4 + (1 + θ ^ 2 + Y + (1 + θ ^ 2) * X) / r) ^ r) :
    False := by
  have hr0 : 0 < r := by omega
  have ht := t_le hr hθ hθr
  have ht1 : (1:ℝ) ≤ θ ^ 2 := one_le_pow₀ (theta_ge_one hr0 hθ hθr)
  set t := θ ^ 2 with htdef
  have htt : t ^ 2 ≤ (1 + 3 / 2325) ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
  have htY : t * Y ≤ (1 + 3 / 2325) * Y := mul_le_mul_of_nonneg_right ht (by linarith)
  have htX : t * X ≤ (1 + 3 / 2325) * X := mul_le_mul_of_nonneg_right ht (by linarith)
  have httX : t ^ 2 * X ≤ (1 + 3 / 2325) ^ 2 * X := mul_le_mul_of_nonneg_right htt (by linarith)
  have hE : (4 + t + t ^ 2 + (4 + t) * Y + (4 + t + t ^ 2) * X) / 4 ≤ 87307 / 10000 := by
    nlinarith
  have hQ0 : 0 ≤ 1 + t + Y + (1 + t) * X := by nlinarith
  have hr' : (2325:ℝ) ≤ r := by exact_mod_cast hr
  have hD : (1 + t + Y + (1 + t) * X) / r ≤ 63 / 10000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 + t + Y + (1 + t) * X ≤ 15 := by nlinarith
    nlinarith
  have hF0 : 0 ≤ (4 + t + t ^ 2 + (4 + t) * Y + (4 + t + t ^ 2) * X) / 4 +
      (1 + t + Y + (1 + t) * X) / r := by positivity
  refine size_contra hr hq hAr hθ hθr hF0 hQ (fun _ => by linarith) (fun hi => ?_)
  have := X_ge hr0 hθ hθr hAr hi
  linarith

/-- **Mixed up/down flips, coprime case.** Let `r ≥ 2325`, `gcd(A, r) = 1`,
`3^r + 1 < 2^A`. Let `k ≠ k'` be sites in `(0, r)` with `ρ = kA mod r`, `ρ' = k'A mod r`
satisfying `2 ≤ ρ'`, `ρ' + 3 ≤ ρ ≤ r - 3` and
`5·4^{(ρ'+1)/r} + 6·4^{(r-ρ+ρ')/r} ≤ 28.9`. If the partial sums of `v` equal those of the
Christoffel word `chr r A` plus one at `k` and minus one at `k'` (agreeing elsewhere below `r`),
then `(2^A - 3^r) ∤ B(v)`. Proof: the relation `2 + 2(g-1)g^p - (g-1)g^{p'} = 0`
(`p = r-1-ρ`, `p' = r-1-ρ'`) times `g^{r-p'}/2` is the pentanomial
`1 - g + g^s - g^m + g^{m+1} = 0` (`s = ρ'+1`, `m = r-ρ+ρ'`) with odd constant term, which the
`NormFlips` Szegő-filtered Hadamard engine excludes. -/
theorem no_cycle_mixed_flips (r A : ℕ) (hr : 2325 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (H1 : 2 ≤ k' * A % r) (H2 : k' * A % r + 3 ≤ k * A % r)
    (H3 : k * A % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * A % r + 1 : ℕ) : ℝ) / r) +
      6 * (4:ℝ) ^ (((r - k * A % r + k' * A % r : ℕ) : ℝ) / r) ≤ 289 / 10)
    (v : ℕ → ℕ) (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  have hnt := nontrivial_q hq
  have hr2 : 2 ≤ r := by omega
  have hr0 : 0 < r := by omega
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
  set ρ := k * A % r with hρ
  set ρ' := k' * A % r with hρ'
  have heq : 2 * G + (g - 1) * (2 * (G * g ^ (r - 1 - ρ)) - G * g ^ (r - 1 - ρ')) = 0 := by
    linear_combination -2 * hK - (g - 1) * hsum
  have hR : 2 + (g - 1) * (2 * g ^ (r - 1 - ρ) - g ^ (r - 1 - ρ')) = 0 :=
    hGu.mul_right_eq_zero.mp (by linear_combination heq)
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
  exact finish_mixed hr hq hAr.le hθ hθr hY1 hX1 (by rw [hY, hX]; exact H4) hE

section Cycle
open CollatzProof

/-- **Cycle form.** No positive `T`-cycle (period `L`, `r ≥ 2325` odd steps, `gcd(L, r) = 1`)
has a valuation word whose partial sums are those of `chr r L` plus one at `k` and minus one at
`k'`, with `ρ = kL mod r`, `ρ' = k'L mod r` in the region of `no_cycle_mixed_flips`. -/
theorem cycle_mixed_flips {m L r : ℕ} {v : ℕ → ℕ} (hr : 2325 ≤ r) (hcop : Nat.Coprime L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (H1 : 2 ≤ k' * L % r) (H2 : k' * L % r + 3 ≤ k * L % r)
    (H3 : k * L % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * L % r + 1 : ℕ) : ℝ) / r) +
      6 * (4:ℝ) ^ (((r - k * L % r + k' * L % r : ℕ) : ℝ) / r) ≤ 289 / 10)
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r L) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) : False := by
  obtain ⟨hq, hdiv⟩ := cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_mixed_flips r L hr hcop hq k k' hk hk' hne H1 H2 H3 H4 v hv hdiv

end Cycle

end CollatzSearch.NormMixed

#print axioms CollatzSearch.NormMixed.mixed_engine
#print axioms CollatzSearch.NormMixed.finish_mixed
#print axioms CollatzSearch.NormMixed.no_cycle_mixed_flips
#print axioms CollatzSearch.NormMixed.cycle_mixed_flips
