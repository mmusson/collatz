import NormGeom
import Mathlib.Algebra.Order.Chebyshev

/-!
# the polynomial (degree-`D` Toeplitz) filter engine

* `poly_filter_engine`: generalises `NormFlips`' `NormFilter.filter_engine` (`D = 1`,
  `w = (1, 1/2)`) to any real filter `w` with `w 0 = 1` of degree `D < r`:
  `q^2 ≤ (Σ_{n<r} pf_n^2 θ^{2n} + D(D+1)·W·Q/r)^r`, where `pf` are the coefficients of
  `w(X)c(X) mod (X^r - 2)`, `W = Σ_{l≤D} w_l^2 θ^{2l}`, `Q = Σ c_n^2 θ^{2n}`. Proof: Hadamard
  after the lower unitriangular Toeplitz column operation `U_{kj} = w_{k-j}θ^{k-j}` (`det 1`);
  the `r - D` full columns have entries `θ^n pf_n`, the `D` partial columns are bounded by
  Cauchy–Schwarz.
* With `w = (20, 13, 8, 5, 2)/20` (`wf`, `Σw² = 662/400`, `Σ(Δw)² = 496/400`) and a
  separated flip sequence (`p ≥ 5`, `p + 6 ≤ r`, pairwise gaps `≥ 6`), the blocks are disjoint
  and `E ≤ θ^{10}(662/400 + (496/400) Σ_P θ^{2p})` (`E_bound`). With `NormBig.size_contra_big`
  (threshold `8.96` at `r ≥ 40901`) this gives `core_sep`: `Σ_P θ^{2p} ≤ 29/5` is impossible
  (engine value `≤ 8.87`).
* `no_cycle_k_right_flips_sep` (T3, word level, coprime, `r ≥ 40901`): any set of separated
  right flips with `Σ 4^{p/r} ≤ 5.8` (`NormFlips`: `≤ 4.9`, unseparated). Reaches five flips.
  `no_cycle_two_right_flips_sep` (two flips) and `cycle_k_right_flips_sep` (cycle form).
* `cycle_two_right_flips_adjacent` (T2e, any `gcd(L, r)`): adjacent right flips at `k, k+1`
  in a cycle word, closing `NormCycleAll`'s open "lower site not an up-site" case except when
  `ρ_k ∈ {1,…,4}` or `ρ_{k+1} ∈ [r-5, r-1]` (at most 9 sites per `(r, L)`).

All results are word-level exclusions near Christoffel words (density zero); not milestones,
no progress on `Goal.lean`. The filter idea is a discrete Szegő / prediction-filter
preconditioning of Hadamard's inequality (standard in spirit); its use here is plausibly new.
-/

namespace CollatzSearch.NormPoly
open Matrix Finset CollatzSearch.NormDet CollatzSearch.NormSparse CollatzSearch.NormFilter

/-- `n`-th coefficient (`n < r`) of `w(X)·c(X)` reduced mod `X^r = 2`, for a filter
`w` of degree `≤ D < r`. -/
noncomputable def pf (r D : ℕ) (w : ℕ → ℝ) (c : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ l ∈ range (D + 1), w l * (if l ≤ n then (c (n - l) : ℝ) else 2 * (c (n + r - l) : ℝ))

/-- The circulant index `i ↦ nn r i j` is a bijection of `Fin r` onto `range r`. -/
theorem sum_nn {r : ℕ} {j : ℕ} (hj : j < r) (f : ℕ → ℝ) :
    ∑ i : Fin r, f (nn r i j) = ∑ n ∈ range r, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (nn r i j))]
  apply Finset.sum_nbij' (fun i => nn r i j) (fun n => if n + j < r then n + j else n + j - r)
  · intro a ha; have := mem_range.mp ha; simp only [mem_range]; unfold nn; split_ifs <;> omega
  · intro a ha; have := mem_range.mp ha; simp only [mem_range]; split_ifs <;> omega
  · intro a ha; have := mem_range.mp ha; unfold nn; split_ifs <;> omega
  · intro a ha; have := mem_range.mp ha; unfold nn; split_ifs <;> omega
  · intro a _; rfl

/-- Reindexing the banded column operation. -/
theorem band_sum {r D j : ℕ} (F : ℕ → ℝ) (w : ℕ → ℝ) (θ : ℝ) :
    ∑ k ∈ range r, F k * (if j ≤ k ∧ k - j ≤ D then w (k - j) * θ ^ (k - j) else 0) =
      ∑ l ∈ range (D + 1), (if j + l < r then F (j + l) * (w l * θ ^ l) else 0) := by
  have h1 : ∀ l ∈ range (D + 1), (if j + l < r then F (j + l) * (w l * θ ^ l) else 0) =
      ∑ k ∈ range r, (if k = j + l then F k * (w l * θ ^ l) else 0) := by
    intro l _
    rw [sum_ite_eq' (range r) (j + l) (fun k => F k * (w l * θ ^ l))]
    simp only [mem_range]
  rw [sum_congr rfl h1, sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases h : j ≤ k ∧ k - j ≤ D
  · rw [if_pos h, sum_eq_single_of_mem (k - j) (mem_range.mpr (by omega))]
    · rw [if_pos (by omega)]
    · intro l _ hl; rw [if_neg (by omega)]
  · rw [if_neg h, mul_zero]
    symm; apply sum_eq_zero; intro l hl
    have := mem_range.mp hl
    rw [if_neg (by omega)]

/-- **Polynomial-filter engine.** Generalises `NormFilter.filter_engine`
(`D = 1`, `w = (1, 1/2)`) to any real filter `w` with `w 0 = 1` of degree `D < r`: if
`q > 1`, `c 0` is odd, `g^r = 2` in `ZMod q` and `Σ_{n<r} c_n g^n = 0`, then for `θ > 0` with
`θ^r = 2`,
`q^2 ≤ (Σ_{n<r} pf_n^2 θ^{2n} + D(D+1)·(Σ_{l≤D} w_l^2 θ^{2l})·(Σ_{n<r} c_n^2 θ^{2n})/r)^r`,
where `pf` are the coefficients of `w(X)c(X)` mod `X^r - 2`. Proof: Hadamard after the lower
unitriangular Toeplitz column operation `U_{kj} = w_{k-j} θ^{k-j}`; the `r - D` full columns
have entries `θ^n pf_n`, the `D` partial ones are bounded by Cauchy–Schwarz. -/
theorem poly_filter_engine {q r D : ℕ} (hq1 : 1 < q) (hr : 2 ≤ r) (hD : D < r) (c : ℕ → ℤ)
    (hc0 : Odd (c 0)) (g : ZMod q) (hg : g ^ r = 2) (h : ∑ n ∈ range r, (c n : ZMod q) * g ^ n = 0)
    (w : ℕ → ℝ) (hw0 : w 0 = 1) (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 ≤ (∑ n ∈ range r, pf r D w c n ^ 2 * θ ^ (2 * n) +
      (D:ℝ) * (D + 1) * (∑ l ∈ range (D + 1), w l ^ 2 * θ ^ (2 * l)) *
        (∑ n ∈ range r, ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)) / r) ^ r := by
  have hr0 : 0 < r := by omega
  have hsq := q_sq_le_det_sq hq1 hr0 c hc0 g hg h
  set M := circ r c with hM
  set d : Fin r → ℝ := fun i => θ ^ (i:ℕ) with hd
  set e : Fin r → ℝ := fun i => (θ ^ (i:ℕ))⁻¹ with he
  set N : Matrix (Fin r) (Fin r) ℝ := diagonal d * M.map (Int.cast : ℤ → ℝ) * diagonal e with hN
  have hNdet : N.det = (M.det : ℝ) := by
    rw [hN, det_mul, det_mul, det_diagonal, det_diagonal, Int.cast_det]
    have : (∏ i, d i) * (∏ i, e i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one; intro i _
      simp only [hd, he]; exact mul_inv_cancel₀ (pow_ne_zero _ hθ.ne')
    calc (∏ i, d i) * (M.map (Int.cast : ℤ → ℝ)).det * ∏ i, e i
        = ((∏ i, d i) * (∏ i, e i)) * (M.map (Int.cast : ℤ → ℝ)).det := by ring
      _ = _ := by rw [this, one_mul]
  set F : ℕ → ℕ → ℝ := fun i m => (c (nn r i m) : ℝ) * θ ^ (nn r i m) with hF
  have hN' : ∀ i k : Fin r, N i k = F i k := by
    intro i k
    have : N i k = θ ^ (i:ℕ) * ((circ r c i k : ℤ) : ℝ) * (θ ^ (k:ℕ))⁻¹ := by
      simp [hN, hM, hd, he, diagonal_mul, mul_diagonal]
    rw [this, N_entry c hθ hθr]
  set Q := ∑ n ∈ range r, ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) with hQ
  have hcolQ : ∀ m, m < r → ∑ i : Fin r, F i m ^ 2 = Q := by
    intro m hm
    rw [show (fun i : Fin r => F i m ^ 2) = fun i : Fin r =>
      (fun n => ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)) (nn r i m) by
        funext i; simp only [hF]; rw [mul_pow, ← pow_mul, mul_comm 2]]
    exact (sum_nn hm (fun n => ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n))).trans hQ.symm
  -- the Toeplitz filter
  set U : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun k j =>
    if (j:ℕ) ≤ k ∧ (k:ℕ) - j ≤ D then w ((k:ℕ) - j) * θ ^ ((k:ℕ) - j) else 0 with hU
  have hUdet : U.det = 1 := by
    rw [det_of_isLowerTriangular]
    · apply Finset.prod_eq_one; intro i _; simp [hU, hw0]
    · intro i j hij
      have : (i:ℕ) < j := hij
      simp only [hU, of_apply]
      rw [if_neg (by omega)]
  have hdet : (N * U).det = (M.det : ℝ) := by rw [det_mul, hUdet, mul_one, hNdet]
  have hNU : ∀ i j : Fin r, (N * U) i j = ∑ l ∈ range (D + 1),
      (if (j:ℕ) + l < r then F i ((j:ℕ) + l) * (w l * θ ^ l) else 0) := by
    intro i j
    rw [mul_apply, ← band_sum]
    rw [← Fin.sum_univ_eq_sum_range (fun k => F i k *
      (if (j:ℕ) ≤ k ∧ k - j ≤ D then w (k - j) * θ ^ (k - j) else 0))]
    apply sum_congr rfl; intro k _
    rw [hN']; simp only [hU, of_apply]
  set E := ∑ n ∈ range r, pf r D w c n ^ 2 * θ ^ (2 * n) with hE
  set W := ∑ l ∈ range (D + 1), w l ^ 2 * θ ^ (2 * l) with hW
  -- full columns
  have hfull : ∀ j : Fin r, (j:ℕ) + D < r → ∑ i : Fin r, (N * U) i j ^ 2 = E := by
    intro j hj
    have hent : ∀ i : Fin r, (N * U) i j = θ ^ (nn r i j) * pf r D w c (nn r i j) := by
      intro i
      rw [hNU, pf, Finset.mul_sum]
      apply sum_congr rfl; intro l hl
      have hl' := mem_range.mp hl
      rw [if_pos (by omega)]
      have hi := i.2
      simp only [hF]
      by_cases hln : l ≤ nn r i j
      · rw [if_pos hln]
        have e1 : nn r i ((j:ℕ) + l) = nn r i j - l := by
          have hln' := hln; have := j.2; unfold nn at hln' ⊢; split_ifs at hln' ⊢ <;> omega
        rw [e1]
        have e2 : θ ^ (nn r i j) = θ ^ (nn r i j - l) * θ ^ l := by
          rw [← pow_add]; congr 1; omega
        rw [e2]; ring
      · rw [if_neg hln]
        have e1 : nn r i ((j:ℕ) + l) = nn r i j + r - l := by
          have hln' := hln; have := j.2; unfold nn at hln' ⊢; split_ifs at hln' ⊢ <;> omega
        rw [e1]
        have e2 : θ ^ (nn r i j + r - l) * θ ^ l = 2 * θ ^ (nn r i j) := by
          rw [← pow_add, show nn r i j + r - l + l = nn r i j + r by omega, pow_add, hθr]; ring
        linear_combination (w l * (c (nn r i j + r - l) : ℝ)) * e2
    simp_rw [hent]
    rw [show (fun i : Fin r => (θ ^ (nn r i j) * pf r D w c (nn r i j)) ^ 2) = fun i : Fin r =>
      (fun n => pf r D w c n ^ 2 * θ ^ (2 * n)) (nn r i j) by
        funext i; rw [mul_pow, ← pow_mul]; ring]
    exact (sum_nn j.2 (fun n => pf r D w c n ^ 2 * θ ^ (2 * n))).trans hE.symm
  -- partial columns
  have hpart : ∀ j : Fin r, ∑ i : Fin r, (N * U) i j ^ 2 ≤ (D + 1) * W * Q := by
    intro j
    have h1 : ∀ i : Fin r, (N * U) i j ^ 2 ≤ (D + 1) * ∑ l ∈ range (D + 1),
        (if (j:ℕ) + l < r then F i ((j:ℕ) + l) * (w l * θ ^ l) else 0) ^ 2 := by
      intro i
      rw [hNU]
      have := sq_sum_le_card_mul_sum_sq (s := range (D + 1))
        (f := fun l => if (j:ℕ) + l < r then F i ((j:ℕ) + l) * (w l * θ ^ l) else 0)
      simpa using this
    calc ∑ i : Fin r, (N * U) i j ^ 2
        ≤ ∑ i : Fin r, (D + 1) * ∑ l ∈ range (D + 1),
          (if (j:ℕ) + l < r then F i ((j:ℕ) + l) * (w l * θ ^ l) else 0) ^ 2 :=
          sum_le_sum fun i _ => h1 i
      _ = (D + 1) * ∑ l ∈ range (D + 1), ∑ i : Fin r,
          (if (j:ℕ) + l < r then F i ((j:ℕ) + l) * (w l * θ ^ l) else 0) ^ 2 := by
          rw [← Finset.mul_sum, sum_comm]
      _ ≤ (D + 1) * ∑ l ∈ range (D + 1), w l ^ 2 * θ ^ (2 * l) * Q := by
          gcongr with l hl
          by_cases hjl : (j:ℕ) + l < r
          · simp_rw [if_pos hjl]
            simp_rw [mul_pow]
            rw [← Finset.sum_mul, hcolQ _ hjl, ← pow_mul, mul_comm l 2]; ring_nf; rfl
          · simp_rw [if_neg hjl]; simp
            have hQ0 : 0 ≤ Q := sum_nonneg fun n _ => by positivity
            positivity
      _ = (D + 1) * W * Q := by rw [hW, mul_assoc, Finset.sum_mul]
  have hE0 : 0 ≤ E := sum_nonneg fun n _ => by positivity
  have hW0 : 0 ≤ W := sum_nonneg fun n _ => by positivity
  have hQ0 : 0 ≤ Q := sum_nonneg fun n _ => by positivity
  have hcolb : ∀ j : Fin r, ∑ i : Fin r, (N * U) i j ^ 2 ≤
      E + (if (j:ℕ) + D < r then 0 else (D + 1) * W * Q) := by
    intro j
    split_ifs with hj
    · rw [hfull j hj, add_zero]
    · linarith [hpart j]
  have hcard : ((range r).filter (fun j => ¬ j + D < r)).card = D := by
    rw [show (range r).filter (fun j => ¬ j + D < r) = Ico (r - D) r by
      ext j; simp only [mem_filter, mem_range, mem_Ico]; omega]
    rw [Nat.card_Ico]; omega
  have hfrob : ∑ i, ∑ j, (N * U) i j ^ 2 ≤ r * E + D * ((D + 1) * W * Q) := by
    rw [Finset.sum_comm]
    calc ∑ j : Fin r, ∑ i : Fin r, (N * U) i j ^ 2
        ≤ ∑ j : Fin r, (E + (if (j:ℕ) + D < r then 0 else (D + 1) * W * Q)) :=
          sum_le_sum fun j _ => hcolb j
      _ = ∑ j ∈ range r, (E + (if j + D < r then 0 else (D + 1) * W * Q)) :=
          Fin.sum_univ_eq_sum_range (fun j => E + (if j + D < r then 0 else (D + 1) * W * Q)) r
      _ = r * E + D * ((D + 1) * W * Q) := by
          rw [sum_add_distrib, sum_const, card_range, sum_ite, sum_const_zero, zero_add,
            sum_const, hcard]; simp only [nsmul_eq_mul]
  have hH := det_sq_mul_le_real (N * U)
  rw [hdet] at hH
  have hrpos : (0:ℝ) < r := by exact_mod_cast hr0
  have hfr : r * E + D * ((D + 1) * W * Q) = (r:ℝ) * (E + D * (D + 1) * W * Q / r) := by
    field_simp
  have h2 : (∑ i, ∑ j, (N * U) i j ^ 2) ^ r ≤ ((r:ℝ) * (E + D * (D + 1) * W * Q / r)) ^ r := by
    rw [← hfr]
    exact pow_le_pow_left₀ (sum_nonneg fun i _ => sum_nonneg fun j _ => by positivity) hfrob r
  rw [mul_pow] at h2
  have hrr : (0:ℝ) < (r:ℝ) ^ r := by positivity
  have h3 : (q:ℝ) ^ 2 * (r:ℝ) ^ r ≤ (r:ℝ) ^ r * (E + D * (D + 1) * W * Q / r) ^ r := by
    calc (q:ℝ) ^ 2 * (r:ℝ) ^ r ≤ ((M.det : ℤ) : ℝ) ^ 2 * (r:ℝ) ^ r :=
          mul_le_mul_of_nonneg_right hsq hrr.le
      _ ≤ _ := hH.trans h2
  nlinarith

/-! ## The degree-4 filter `w = (20, 13, 8, 5, 2)/20` on separated flips -/

/-- The degree-4 filter `w = (1, 13/20, 2/5, 1/4, 1/10)` (zero beyond degree 4). -/
noncomputable def wf (l : ℕ) : ℝ :=
  if l = 0 then 1 else if l = 1 then 13 / 20 else if l = 2 then 2 / 5 else
    if l = 3 then 1 / 4 else if l = 4 then 1 / 10 else 0

theorem wf_zero {l : ℕ} (h : 4 < l) : wf l = 0 := by
  unfold wf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- Shifted filter `X^a w(X)`, coefficient `n`. -/
noncomputable def sa (a n : ℕ) : ℝ := if a ≤ n then wf (n - a) else 0

/-- Block of one flip: coefficients of `(X - 1) w(X)`, i.e. `(-1, 7/20, 1/4, 3/20, 3/20, 1/10)`. -/
noncomputable def blk (j : ℕ) : ℝ := (if 1 ≤ j then wf (j - 1) else 0) - wf j

theorem blk_zero {j : ℕ} (h : 5 < j) : blk j = 0 := by
  unfold blk; rw [if_pos (by omega), wf_zero (by omega), wf_zero (by omega)]; ring

/-- No wrap-around when `c` vanishes on `[r - D, ∞)`. -/
theorem pf_nowrap {r D : ℕ} (w : ℕ → ℝ) (c : ℕ → ℤ) (hc : ∀ m, r - D ≤ m → c m = 0) (n : ℕ) :
    pf r D w c n = ∑ l ∈ range (D + 1), w l * (if l ≤ n then (c (n - l) : ℝ) else 0) := by
  unfold pf
  apply sum_congr rfl; intro l hl
  have := mem_range.mp hl
  split_ifs with h
  · rfl
  · rw [hc _ (by omega)]; simp

theorem conv_ind (a n : ℕ) :
    ∑ l ∈ range 5, wf l * (if l ≤ n then ((NormSparse.ind a (n - l) : ℤ) : ℝ) else 0) = sa a n := by
  unfold sa
  by_cases h : a ≤ n ∧ n - a ≤ 4
  · rw [sum_eq_single_of_mem (n - a) (mem_range.mpr (by omega))]
    · rw [if_pos (by omega), if_pos h.1]
      simp [NormSparse.ind, show n - (n - a) = a by omega]
    · intro l _ hl
      split_ifs with h1
      · simp [NormSparse.ind, show n - l ≠ a by omega]
      · simp
  · have hr : (if a ≤ n then wf (n - a) else 0) = 0 := by
      split_ifs with h1
      · exact wf_zero (by omega)
      · rfl
    rw [hr]
    apply sum_eq_zero; intro l hl
    have := mem_range.mp hl
    split_ifs with h1
    · simp [NormSparse.ind, show n - l ≠ a by omega]
    · simp

/-- `pf` of a separated flip sequence: `pf_n = sa 0 n + Σ_{p∈P} (sa (p+1) n - sa p n)`. -/
theorem pf_cP {r : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p + 6 ≤ r) (hr : 5 ≤ r) (n : ℕ) :
    pf r 4 wf (cP P) n = sa 0 n + ∑ p ∈ P, (sa (p + 1) n - sa p n) := by
  have hc : ∀ m, r - 4 ≤ m → cP P m = 0 := by
    intro m hm
    unfold cP
    rw [show NormSparse.ind 0 m = 0 by simp [NormSparse.ind]; omega, zero_add]
    apply sum_eq_zero; intro p hp
    have := hP p hp
    simp [NormSparse.ind]; omega
  rw [pf_nowrap wf (cP P) hc n, show (4:ℕ) + 1 = 5 by rfl]
  have term : ∀ l, wf l * (if l ≤ n then ((cP P (n - l) : ℤ) : ℝ) else 0) =
      wf l * (if l ≤ n then ((NormSparse.ind 0 (n - l) : ℤ) : ℝ) else 0) +
      ∑ p ∈ P, (wf l * (if l ≤ n then ((NormSparse.ind (p + 1) (n - l) : ℤ) : ℝ) else 0) -
        wf l * (if l ≤ n then ((NormSparse.ind p (n - l) : ℤ) : ℝ) else 0)) := by
    intro l
    split_ifs
    · unfold cP; push_cast; rw [mul_add, Finset.mul_sum]; congr 1
      apply sum_congr rfl; intro p _; ring
    · simp
  rw [sum_congr rfl fun l _ => term l, sum_add_distrib, sum_comm, conv_ind]
  congr 1
  apply sum_congr rfl; intro p _
  rw [sum_sub_distrib, conv_ind, conv_ind]

theorem bp_eq (p n : ℕ) : sa (p + 1) n - sa p n = if p ≤ n then blk (n - p) else 0 := by
  unfold sa blk
  by_cases h1 : p + 1 ≤ n
  · rw [if_pos h1, if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show n - p - 1 = n - (p + 1) by omega]
  · by_cases h2 : p ≤ n
    · rw [if_neg h1, if_pos h2, if_pos h2, if_neg (by omega)]
    · rw [if_neg h1, if_neg h2, if_neg h2]; ring

/-- Disjoint supports: with all `p ≥ 5` and pairwise separation `≥ 6`, the square of
`pf_n` is the sum of the squares of its blocks. -/
theorem pf_sq {P : Finset ℕ} (hP5 : ∀ p ∈ P, 5 ≤ p)
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → p + 6 ≤ p' ∨ p' + 6 ≤ p) (n : ℕ) :
    (sa 0 n + ∑ p ∈ P, (if p ≤ n then blk (n - p) else 0)) ^ 2 =
      sa 0 n ^ 2 + ∑ p ∈ P, (if p ≤ n then blk (n - p) else 0) ^ 2 := by
  by_cases hex : ∃ p0 ∈ P, p0 ≤ n ∧ n ≤ p0 + 5
  · obtain ⟨p0, hp0, h1, h2⟩ := hex
    have hs0 : sa 0 n = 0 := by
      unfold sa; rw [if_pos (by omega), wf_zero (by have := hP5 p0 hp0; omega)]
    have hoth : ∀ p ∈ P, p ≠ p0 → (if p ≤ n then blk (n - p) else 0) = 0 := by
      intro p hp hne
      have := hsep p hp p0 hp0 hne
      split_ifs with h
      · exact blk_zero (by omega)
      · rfl
    rw [hs0, sum_eq_single_of_mem p0 hp0 hoth,
      sum_eq_single_of_mem p0 hp0 (fun p hp hne => by rw [hoth p hp hne]; ring)]
    ring
  · push Not at hex
    have hall : ∀ p ∈ P, (if p ≤ n then blk (n - p) else 0) = 0 := by
      intro p hp
      split_ifs with h
      · exact blk_zero (by have := hex p hp h; omega)
      · rfl
    rw [sum_eq_zero hall, sum_eq_zero (fun p hp => by rw [hall p hp]; ring)]
    ring

theorem head_bound {r : ℕ} (hr : 5 ≤ r) {θ : ℝ} (hθ1 : 1 ≤ θ) :
    ∑ n ∈ range r, sa 0 n ^ 2 * θ ^ (2 * n) ≤ θ ^ 10 * (662 / 400) := by
  rw [← sum_range_add_sum_Ico _ hr]
  have hz : ∑ n ∈ Ico 5 r, sa 0 n ^ 2 * θ ^ (2 * n) = 0 := by
    apply sum_eq_zero; intro n hn
    have := (mem_Ico.mp hn).1
    unfold sa; rw [if_pos (by omega), wf_zero (by omega)]; ring
  rw [hz, add_zero]
  simp only [sum_range_succ, sum_range_zero, sa, wf]
  norm_num
  have h2 : θ ^ 2 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h4 : θ ^ 4 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h6 : θ ^ 6 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h8 : θ ^ 8 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h0 : 1 ≤ θ ^ 10 := one_le_pow₀ hθ1
  linarith

theorem block_bound {r p : ℕ} (hp : p + 6 ≤ r) {θ : ℝ} (hθ1 : 1 ≤ θ) :
    ∑ n ∈ range r, (if p ≤ n then blk (n - p) else 0) ^ 2 * θ ^ (2 * n) ≤
      θ ^ (2 * p) * (θ ^ 10 * (496 / 400)) := by
  rw [← sum_range_add_sum_Ico _ (show p ≤ r by omega),
    ← sum_Ico_consecutive _ (show p ≤ p + 6 by omega) hp]
  have hz1 : ∑ n ∈ range p, (if p ≤ n then blk (n - p) else 0) ^ 2 * θ ^ (2 * n) = 0 := by
    apply sum_eq_zero; intro n hn
    rw [if_neg (by have := mem_range.mp hn; omega)]; ring
  have hz2 : ∑ n ∈ Ico (p + 6) r, (if p ≤ n then blk (n - p) else 0) ^ 2 * θ ^ (2 * n) = 0 := by
    apply sum_eq_zero; intro n hn
    have := (mem_Ico.mp hn).1
    rw [if_pos (by omega), blk_zero (by omega)]; ring
  rw [hz1, hz2, zero_add, add_zero, sum_Ico_eq_sum_range, show p + 6 - p = 6 by omega]
  simp only [sum_range_succ, sum_range_zero, if_pos (Nat.le_add_right p _),
    Nat.add_sub_cancel_left, blk, wf, mul_add, pow_add]
  norm_num
  have hp0 : 0 ≤ θ ^ (2 * p) := by positivity
  have h2 : θ ^ 2 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h4 : θ ^ 4 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h6 : θ ^ 6 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h8 : θ ^ 8 ≤ θ ^ 10 := pow_le_pow_right₀ hθ1 (by norm_num)
  have h0 : 1 ≤ θ ^ 10 := one_le_pow₀ hθ1
  nlinarith [mul_le_mul_of_nonneg_left h2 hp0, mul_le_mul_of_nonneg_left h4 hp0,
    mul_le_mul_of_nonneg_left h6 hp0, mul_le_mul_of_nonneg_left h8 hp0,
    mul_le_mul_of_nonneg_left h0 hp0]

/-- **Filtered energy of separated flips.** For `P` with all `p ≥ 5`, `p + 6 ≤ r` and pairwise
separation `≥ 6`: `Σ_{n<r} pf_n^2 θ^{2n} ≤ θ^{10}(662/400 + (496/400) Σ_{p∈P} θ^{2p})`. -/
theorem E_bound {r : ℕ} (hr : 5 ≤ r) {θ : ℝ} (hθ1 : 1 ≤ θ) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 5 ≤ p ∧ p + 6 ≤ r)
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → p + 6 ≤ p' ∨ p' + 6 ≤ p) :
    ∑ n ∈ range r, pf r 4 wf (cP P) n ^ 2 * θ ^ (2 * n) ≤
      θ ^ 10 * (662 / 400 + 496 / 400 * ∑ p ∈ P, θ ^ (2 * p)) := by
  have hpt : ∀ n, pf r 4 wf (cP P) n ^ 2 * θ ^ (2 * n) =
      sa 0 n ^ 2 * θ ^ (2 * n) +
        ∑ p ∈ P, (if p ≤ n then blk (n - p) else 0) ^ 2 * θ ^ (2 * n) := by
    intro n
    rw [pf_cP (fun p hp => (hP p hp).2) hr n]
    simp_rw [bp_eq]
    rw [pf_sq (fun p hp => (hP p hp).1) hsep n, add_mul, Finset.sum_mul]
  rw [sum_congr rfl fun n _ => hpt n, sum_add_distrib, sum_comm]
  have h1 := head_bound hr hθ1 (θ := θ)
  have h2 : ∑ p ∈ P, ∑ n ∈ range r, (if p ≤ n then blk (n - p) else 0) ^ 2 * θ ^ (2 * n) ≤
      ∑ p ∈ P, θ ^ (2 * p) * (θ ^ 10 * (496 / 400)) :=
    sum_le_sum fun p hp => block_bound (hP p hp).2 hθ1
  have h3 : ∑ p ∈ P, θ ^ (2 * p) * (θ ^ 10 * (496 / 400)) =
      θ ^ 10 * (496 / 400) * ∑ p ∈ P, θ ^ (2 * p) := by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro p _; ring
  rw [h3] at h2
  nlinarith

theorem W_bound {θ : ℝ} (hθ1 : 1 ≤ θ) :
    ∑ l ∈ range (4 + 1), wf l ^ 2 * θ ^ (2 * l) ≤ θ ^ 10 * (662 / 400) := by
  have := head_bound (r := 5) le_rfl hθ1
  simpa [sa] using this

/-- `θ^{2(A-r)} > 9/4` when `3^r < 2^A`, `θ^r = 2`. -/
theorem X_gt {r A : ℕ} {θ : ℝ} (hθ : 0 < θ) (hθr : θ ^ r = 2) (hAr : r ≤ A)
    (h3 : 3 ^ r < 2 ^ A) : 9 / 4 < θ ^ (2 * (A - r)) := by
  have h4 := NormTwo.fourX (A := A) hθr hAr
  by_contra hc
  push Not at hc
  have hle : (4 * θ ^ (2 * (A - r))) ^ r ≤ (9:ℝ) ^ r :=
    pow_le_pow_left₀ (by positivity) (by linarith) r
  rw [h4] at hle
  have e1 : ((3 ^ r : ℕ) : ℝ) < ((2 ^ A : ℕ) : ℝ) := by exact_mod_cast h3
  have e2 : ((3 ^ r : ℕ) : ℝ) ^ 2 < ((2 ^ A : ℕ) : ℝ) ^ 2 :=
    pow_lt_pow_left₀ e1 (by positivity) two_ne_zero
  have e3 : ((3 ^ r : ℕ) : ℝ) ^ 2 = (9:ℝ) ^ r := by
    push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  linarith

/-- **Core: separated right flips with the degree-4 filter.** For `r ≥ 40901`,
`3^r + 1 < 2^A`, `g^r = 2` in `ZMod (2^A - 3^r)`: no finite `P` with all `p ≥ 5`, `p + 6 ≤ r`,
pairwise separation `≥ 6` and `Σ_{p∈P} θ^{2p} ≤ 29/5` satisfies `1 + (g-1) Σ_P g^p = 0`. -/
theorem core_sep {r A : ℕ} (hr : 40901 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A)
    {g : ZMod (2 ^ A - 3 ^ r)} (hg : g ^ r = 2) {θ : ℝ} (hθ : 0 < θ) (hθr : θ ^ r = 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 5 ≤ p ∧ p + 6 ≤ r)
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → p + 6 ≤ p' ∨ p' + 6 ≤ p)
    (hS : ∑ p ∈ P, θ ^ (2 * p) ≤ 29 / 5)
    (hrel : 1 + (g - 1) * ∑ p ∈ P, g ^ p = 0) : False := by
  have hAr := NormReduce.r_lt_A hq
  have hr0 : 0 < r := by omega
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  have hc := rel_cP hr0 g (P := P) (fun p hp => by have := hP p hp; omega)
  rw [hrel] at hc
  have hc0 : Odd (cP P 0) := by
    rw [cP_zero (fun p hp => by have := hP p hp; omega)]; decide
  have hE := poly_filter_engine (D := 4) hq1 (by omega) (by omega) (cP P) hc0 g hg hc wf
    (by simp [wf]) θ hθ hθr
  set E := ∑ n ∈ range r, pf r 4 wf (cP P) n ^ 2 * θ ^ (2 * n) with hEdef
  set W := ∑ l ∈ range (4 + 1), wf l ^ 2 * θ ^ (2 * l) with hWdef
  set Q := ∑ n ∈ range r, ((cP P n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) with hQdef
  set S := ∑ p ∈ P, θ ^ (2 * p) with hSdef
  have hθ1 := NormTwo.theta_ge_one hr0 hθ hθr
  have hS0 : 0 ≤ S := sum_nonneg fun p _ => by positivity
  have hE1 := E_bound (r := r) (by omega) hθ1 hP hsep
  have hW1 := W_bound hθ1
  have hQ1 := gram_c (r := r) (by omega) hθ P (fun p hp => by have := hP p hp; omega)
  have ht := NormBig.t_le_big hr hθ hθr
  have ht1 : 1 ≤ θ ^ 2 := one_le_pow₀ hθ1
  have h10 : θ ^ 10 ≤ 10003669 / 10000000 := by
    have : θ ^ 10 = (θ ^ 2) ^ 5 := by rw [← pow_mul]
    rw [this]
    calc (θ ^ 2) ^ 5 ≤ (1 + 3 / 40901) ^ 5 := pow_le_pow_left₀ (by positivity) ht 5
      _ ≤ 10003669 / 10000000 := by norm_num
  have hEb : E ≤ 10003669 / 10000000 * (662 / 400 + 496 / 400 * (29 / 5)) :=
    hE1.trans (mul_le_mul h10 (by linarith) (by positivity) (by norm_num))
  have hWb : W ≤ 10003669 / 10000000 * (662 / 400) :=
    hW1.trans (mul_le_mul_of_nonneg_right h10 (by norm_num))
  have hQb : Q ≤ 1 + (2 + 3 / 40901) * (29 / 5) := by
    refine hQ1.trans ?_
    have := mul_le_mul (show 1 + θ ^ 2 ≤ 2 + 3 / 40901 by linarith) hS (by positivity)
      (by norm_num)
    linarith
  have hW0 : 0 ≤ W := sum_nonneg fun l _ => by positivity
  have hQ0 : 0 ≤ Q := sum_nonneg fun n _ => by positivity
  have hE0 : 0 ≤ E := sum_nonneg fun n _ => by positivity
  have hrR : (40901:ℝ) ≤ r := by exact_mod_cast hr
  have hWQ : W * Q ≤ (10003669 / 10000000 * (662 / 400)) * (1 + (2 + 3 / 40901) * (29 / 5)) :=
    mul_le_mul hWb hQb hQ0 (by norm_num)
  have hF : ((4:ℕ):ℝ) * ((4:ℕ) + 1) * W * Q / r ≤
      20 * ((10003669 / 10000000 * (662 / 400)) * (1 + (2 + 3 / 40901) * (29 / 5))) / 40901 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast
    have : 0 ≤ W * Q := mul_nonneg hW0 hQ0
    nlinarith
  set F := E + ((4:ℕ):ℝ) * ((4:ℕ) + 1) * W * Q / r with hFdef
  have hFle : F ≤ 887 / 100 := by
    have := add_le_add hEb hF
    refine le_trans (by rw [hFdef]) (this.trans (by norm_num))
  have hF0 : 0 ≤ F := by
    have : 0 ≤ ((4:ℕ):ℝ) * ((4:ℕ) + 1) * W * Q / r := by positivity
    linarith
  have hX := X_gt hθ hθr hAr.le (by omega)
  exact NormBig.size_contra_big hr hq hAr.le hθ hθr hF0 hE
    (fun _ => by linarith) (fun _ => by nlinarith)

section Word
open CollatzSearch.NormGoal CollatzSearch.NormBridge CollatzSearch.NormReduce
  CollatzSearch.NormTwo CollatzSearch.NormFlips

/-- **`k` separated right flips with `Σ 4^{p/r} ≤ 29/5` (word level).**
Let `r ≥ 40901`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`, and `K` a set of sites in `(0, r)` with
exponents `p_k = r - 1 - kA mod r` satisfying `5 ≤ p_k`, `p_k + 6 ≤ r`, pairwise
`|p_k - p_{k'}| ≥ 6`, and `Σ_{k∈K} 4^{p_k/r} ≤ 29/5`. If the partial sums of `v` are those of
`chr r A` plus one on `K`, then `2^A - 3^r ∤ B(v)`. (`NormFlips`/`NormCycleAll`: `Σ ≤ 4.9`, no separation;
the degree-4 filter raises the bound to `5.8`, reaching five flips.) -/
theorem no_cycle_k_right_flips_sep (r A : ℕ) (hr : 40901 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (K : Finset ℕ) (hKr : ∀ k ∈ K, 0 < k ∧ k < r)
    (hpos : ∀ k ∈ K, 5 ≤ r - 1 - k * A % r ∧ r - 1 - k * A % r + 6 ≤ r)
    (hsep : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' →
      r - 1 - k * A % r + 6 ≤ r - 1 - k' * A % r ∨ r - 1 - k' * A % r + 6 ≤ r - 1 - k * A % r)
    (hS : ∑ k ∈ K, (4:ℝ) ^ (((r - 1 - k * A % r : ℕ) : ℝ) / r) ≤ 29 / 5)
    (v : ℕ → ℕ) (hv : ∀ i < r, psum v i = psum (NormGoal.chr r A) i + (if i ∈ K then 1 else 0)) :
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
  have hGu : IsUnit G := (isUnit_g (by omega) hq h2).pow _
  have hBv : (Bnum r v : ZMod (2 ^ A - 3 ^ r)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hBw := cast_Bnum (R := ZMod (2 ^ A - 3 ^ r)) r (NormGoal.chr r A)
  set Fw : ℕ → ZMod (2 ^ A - 3 ^ r) := fun i => 3 ^ (r - 1 - i) * 2 ^ psum (NormGoal.chr r A) i with hFw
  have hpt : ∀ i ∈ range r, (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum v i =
      Fw i + (if i ∈ K then Fw i else 0) := by
    intro i hi
    have hvi := hv i (mem_range.mp hi)
    by_cases e : i ∈ K
    · rw [if_pos e] at hvi ⊢; simp only [hFw]; rw [hvi, pow_succ]; ring
    · rw [if_neg e] at hvi ⊢; simp only [hFw]; rw [hvi]; ring
  have hKsub : K ⊆ range r := fun k hk => mem_range.mpr (hKr k hk).2
  have hsum : (Bnum r v : ZMod (2 ^ A - 3 ^ r)) =
      (Bnum r (NormGoal.chr r A) : ZMod (2 ^ A - 3 ^ r)) + ∑ k ∈ K, Fw k := by
    rw [cast_Bnum, sum_congr rfl hpt, sum_add_distrib, sum_ite_mem, inter_eq_right.mpr hKsub, hBw]
  set pk : ℕ → ℕ := fun k => r - 1 - k * A % r with hpk
  have hF : ∑ k ∈ K, Fw k = G * ∑ k ∈ K, g ^ pk k := by
    rw [Finset.mul_sum]; exact sum_congr rfl fun k hk => term_chr h2 h3 hA1 (hKr k hk).2
  rw [hBv, hF] at hsum
  have hβ : 1 + (g - 1) * ∑ k ∈ K, g ^ pk k = 0 := by
    apply hGu.mul_right_eq_zero.mp
    linear_combination -hK - (g - 1) * hsum
  have hinj : Set.InjOn pk (K : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := hKr x hx; have hy' := hKr y hy
    have m1 := Nat.mod_lt (x * A) hr0; have m2 := Nat.mod_lt (y * A) hr0
    simp only [hpk] at hxy
    exact mod_inj hcop hx'.2 hy'.2 (by omega)
  set P := K.image pk with hP
  set θ : ℝ := (2:ℝ) ^ ((r:ℝ)⁻¹) with hθdef
  have hθ : 0 < θ := by positivity
  have hθr : θ ^ r = 2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
  have hSP : ∑ p ∈ P, θ ^ (2 * p) ≤ 29 / 5 := by
    rw [hP, sum_image hinj]
    calc ∑ k ∈ K, θ ^ (2 * pk k) = ∑ k ∈ K, (4:ℝ) ^ (((r - 1 - k * A % r : ℕ) : ℝ) / r) :=
          sum_congr rfl fun k _ => theta_pow_eq hr0
      _ ≤ 29 / 5 := hS
  have hrelP : 1 + (g - 1) * ∑ p ∈ P, g ^ p = 0 := by rw [hP, sum_image hinj]; exact hβ
  have hPp : ∀ p ∈ P, 5 ≤ p ∧ p + 6 ≤ r := by
    intro p hp; rw [hP, mem_image] at hp; obtain ⟨k, hk, rfl⟩ := hp; exact hpos k hk
  have hPsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → p + 6 ≤ p' ∨ p' + 6 ≤ p := by
    intro p hp p' hp' hne
    rw [hP, mem_image] at hp hp'
    obtain ⟨k, hk, rfl⟩ := hp; obtain ⟨k', hk', rfl⟩ := hp'
    exact hsep k hk k' hk' (fun e => hne (by rw [e]))
  exact core_sep hr hq h2 hθ hθr P hPp hPsep hSP hrelP

/-- **Two separated right flips (word level).** The case `K = {k₁, k₂}` of
`no_cycle_k_right_flips_sep`, with no up-site conditions: `p_i ≥ 5`, `p_i + 6 ≤ r`,
`|p₁ - p₂| ≥ 6`, `4^{p₁/r} + 4^{p₂/r} ≤ 29/5`. -/
theorem no_cycle_two_right_flips_sep (r A : ℕ) (hr : 40901 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r)
    (hne : k₁ ≠ k₂)
    (hp1 : 5 ≤ r - 1 - k₁ * A % r ∧ r - 1 - k₁ * A % r + 6 ≤ r)
    (hp2 : 5 ≤ r - 1 - k₂ * A % r ∧ r - 1 - k₂ * A % r + 6 ≤ r)
    (hsep : r - 1 - k₁ * A % r + 6 ≤ r - 1 - k₂ * A % r ∨
      r - 1 - k₂ * A % r + 6 ≤ r - 1 - k₁ * A % r)
    (hS : (4:ℝ) ^ (((r - 1 - k₁ * A % r : ℕ) : ℝ) / r) +
      (4:ℝ) ^ (((r - 1 - k₂ * A % r : ℕ) : ℝ) / r) ≤ 29 / 5)
    (v : ℕ → ℕ)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r A) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  apply no_cycle_k_right_flips_sep r A hr hcop hq {k₁, k₂}
  · intro k hk; simp only [mem_insert, mem_singleton] at hk; rcases hk with rfl | rfl <;> omega
  · intro k hk; simp only [mem_insert, mem_singleton] at hk; rcases hk with rfl | rfl <;> assumption
  · intro k hk k' hk' hkk
    simp only [mem_insert, mem_singleton] at hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl
    · exact absurd rfl hkk
    · exact hsep
    · exact hsep.symm
    · exact absurd rfl hkk
  · rw [sum_pair hne]; exact hS
  · intro i hi; rw [hv i hi]; congr 1; simp only [mem_insert, mem_singleton]

end Word

section Cycle
open CollatzProof CollatzSearch.NormGoal CollatzSearch.NormBridge CollatzSearch.NormCycleAll

/-- **Cycle form of `no_cycle_k_right_flips_sep` (coprime).** No positive `T`-cycle
point `m ≠ 1` with `gcd(L, r) = 1` has a valuation word obtained from `chr r L` by `+1`
partial-sum flips on a set `K` of sites in `(0, r)` whose exponents `p_k = r - 1 - kL mod r`
satisfy `5 ≤ p_k`, `p_k + 6 ≤ r`, pairwise separation `≥ 6` and `Σ 4^{p_k/r} ≤ 29/5`. -/
theorem cycle_k_right_flips_sep {m L r : ℕ} {v : ℕ → ℕ} (hcop : Nat.Coprime L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1) (K : Finset ℕ) (hK1 : K.Nonempty) (hKr : ∀ k ∈ K, 0 < k ∧ k < r)
    (hpos : ∀ k ∈ K, 5 ≤ r - 1 - k * L % r ∧ r - 1 - k * L % r + 6 ≤ r)
    (hsep : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' →
      r - 1 - k * L % r + 6 ≤ r - 1 - k' * L % r ∨ r - 1 - k' * L % r + 6 ≤ r - 1 - k * L % r)
    (hS : ∑ k ∈ K, (4:ℝ) ^ (((r - 1 - k * L % r : ℕ) : ℝ) / r) ≤ 29 / 5)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i ∈ K then 1 else 0)) : False := by
  have hr1 : 1 ≤ r := by
    obtain ⟨k, hk⟩ := hK1; have := hKr k hk; omega
  obtain ⟨_, hrb⟩ := cycle_params hr1 hv1 hL hodd hcyc hm
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_k_right_flips_sep r L hrb hcop hq K hKr hpos hsep hS
    v hv hdiv

/-- `L ≥ r + 6` whenever `3^r < 2^L` and `r ≥ 9`. -/
theorem L_ge_r6 {r L : ℕ} (hr : 9 ≤ r) (h : 3 ^ r < 2 ^ L) : r + 6 ≤ L := by
  by_contra hc
  have h1 : 2 ^ L ≤ 2 ^ (r + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (r - 9) ≤ 3 ^ (r - 9) := Nat.pow_le_pow_left (by norm_num) _
  have h3 : 3 ^ r = 3 ^ (r - 9) * 3 ^ 9 := by rw [← pow_add]; congr 1; omega
  have h4 : 2 ^ (r + 5) = 2 ^ (r - 9) * 2 ^ 14 := by rw [← pow_add]; congr 1; omega
  have : 2 ^ (r - 9) * 2 ^ 14 < 3 ^ (r - 9) * 3 ^ 9 := by
    calc 2 ^ (r - 9) * 2 ^ 14 ≤ 3 ^ (r - 9) * 2 ^ 14 := Nat.mul_le_mul_right _ h2
      _ < 3 ^ (r - 9) * 3 ^ 9 := by
        apply Nat.mul_lt_mul_of_pos_left (by norm_num) (by positivity)
  omega

/-- **Adjacent two right flips for cycles (any `gcd(L, r)`).** No positive
`T`-cycle point `m ≠ 1` (period `L`, `r` odd steps) has a valuation word whose partial sums are
those of `chr r L` plus one at two adjacent sites `k, k+1` (`0 < k`, `k + 1 < r`), unless
the lower site is not an up-site (`ρ + a < r`, `ρ = kL mod r`, `a = L mod r`) and
`ρ ∈ {1,…,4}` or `ρ + a ∈ [r-5, r-1]` (the open residues). Proof: if `k` is an up-site this
is `cycle_two_right_flips_uncond`; if `gcd(L, r) ≥ 2` it is `NormCofactor`'s
`cycle_two_site_noncoprime`; otherwise the exponents are `b = r-1-ρ` and `b - a` with
`4^{b/r} + 4^{(b-a)/r} < 4(1 + 4/9) = 52/9 ≤ 29/5` (as `4^{a/r} > 9/4`), and
`no_cycle_two_right_flips_sep` (degree-4 filter) applies. -/
theorem cycle_two_right_flips_adjacent {m L r : ℕ} {v : ℕ → ℕ}
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1) (k : ℕ) (hk0 : 0 < k) (hk : k + 1 < r)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i = k ∨ i = k + 1 then 1 else 0))
    (h : r ≤ k * L % r + L % r ∨ (5 ≤ k * L % r ∧ k * L % r + L % r + 6 ≤ r)) : False := by
  obtain ⟨hL2, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  have hrL := NormReduce.r_lt_A hq
  have hr0 : 0 < r := by omega
  rcases h with hs1 | ⟨h5, h6⟩
  · have hs2 := up_site_of_valid (S := fun i => i = k ∨ i = k + 1) hrL hL2 hv1 hL hv hk
      (Or.inr rfl) (by omega)
    exact cycle_two_right_flips_uncond hv1 hL hodd hcyc hm k (k + 1) hk0 (by omega) (by omega) hk
      (by omega) hs1 hs2 hv
  rcases Nat.lt_or_ge (Nat.gcd L r) 2 with hd | hd
  swap
  · apply NormCofactor.cycle_two_site_noncoprime (by omega) hd hv1 hL hodd hcyc k (k + 1) hk0
      (by omega) hk 1 1 (Or.inl rfl) (Or.inl rfl)
    intro i hi
    rw [hv i hi]
    push_cast
    by_cases e1 : i = k
    · rw [if_pos (Or.inl e1), if_pos e1, if_neg (by omega)]; ring
    · by_cases e2 : i = k + 1
      · rw [if_pos (Or.inr e2), if_neg e1, if_pos e2]; ring
      · rw [if_neg (by tauto), if_neg e1, if_neg e2]; ring
  have hcop := coprime_of_gcd_lt_two hr0 hd
  set ρ := k * L % r with hρ
  set a := L % r with ha
  have hmod : (k + 1) * L % r = ρ + a := by
    rw [NormReduce.mod_succ hr0 k, if_neg (by omega)]
  have ha_eq : a = L - r := by
    rw [ha, Nat.mod_eq_sub_mod hrL.le, Nat.mod_eq_of_lt (by omega)]
  have ha6 : 6 ≤ a := by have := L_ge_r6 (by omega) (show 3 ^ r < 2 ^ L by omega); omega
  apply no_cycle_two_right_flips_sep r L hrb hcop hq k (k + 1) hk0 (by omega) (by omega) hk
    (by omega)
  · omega
  · rw [hmod]; omega
  · rw [hmod]; omega
  · -- the sum bound
    rw [hmod]
    set θ : ℝ := (2:ℝ) ^ ((r:ℝ)⁻¹) with hθdef
    have hθ : 0 < θ := by positivity
    have hθr : θ ^ r = 2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
    rw [← NormFlips.theta_pow_eq hr0, ← NormFlips.theta_pow_eq hr0]
    have hX := X_gt hθ hθr hrL.le (show 3 ^ r < 2 ^ L by omega)
    rw [← ha_eq] at hX
    have hb4 : θ ^ (2 * (r - 1 - ρ)) ≤ 4 := by
      have h1 := NormTwo.theta_pow_mono hr0 hθ hθr (show r - 1 - ρ ≤ r by omega)
      have h2 : θ ^ (2 * r) = 4 := by rw [mul_comm, pow_mul, hθr]; norm_num
      linarith
    have hsplit : θ ^ (2 * (r - 1 - (ρ + a))) * θ ^ (2 * a) = θ ^ (2 * (r - 1 - ρ)) := by
      rw [← pow_add]; congr 1; omega
    have hp0 : 0 ≤ θ ^ (2 * (r - 1 - (ρ + a))) := by positivity
    show θ ^ (2 * (r - 1 - ρ)) + θ ^ (2 * (r - 1 - (ρ + a))) ≤ 29 / 5
    nlinarith
  · intro i hi; rw [hv i hi]
  · exact hdiv

end Cycle

end CollatzSearch.NormPoly

#print axioms CollatzSearch.NormPoly.sum_nn
#print axioms CollatzSearch.NormPoly.band_sum
#print axioms CollatzSearch.NormPoly.poly_filter_engine
#print axioms CollatzSearch.NormPoly.pf_cP
#print axioms CollatzSearch.NormPoly.E_bound
#print axioms CollatzSearch.NormPoly.W_bound
#print axioms CollatzSearch.NormPoly.X_gt
#print axioms CollatzSearch.NormPoly.core_sep
#print axioms CollatzSearch.NormPoly.no_cycle_k_right_flips_sep
#print axioms CollatzSearch.NormPoly.no_cycle_two_right_flips_sep
#print axioms CollatzSearch.NormPoly.cycle_k_right_flips_sep
#print axioms CollatzSearch.NormPoly.L_ge_r6
#print axioms CollatzSearch.NormPoly.cycle_two_right_flips_adjacent
