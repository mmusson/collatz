import NormTwo

/-!
# the Szegő-filtered sparse engine

* `filter_engine`: Hadamard after a unitriangular column operation. With `N = D M E` the
  conjugated circulant of `NormTwo` (`N_ij = c_n θ^n`, `n = (i-j) mod r`) and
  `U = I + (θ/2)·subdiag` (lower unitriangular, `det U = 1`), every column `j < r-1` of `N U`
  is `½ (e_n θ^n)` with `e` the coefficients of `(2+z)P(z)` mod `z^r = 2`
  (`efil`), and the last column is unchanged. Frobenius AM–GM then gives
  `q^2 r^r ≤ ((r-1)·¼Σ e_n^2 θ^{2n} + Σ c_n^2 θ^{2n})^r`; `filter_engine'` is the normalised
  form `q^2 ≤ (Q' + Q/r)^r`. This strictly improves `NormSparse.sparse_engine` whenever
  `Q' < Q`: a flip cluster `(-1,+1)` becomes `(-1,½,½)` (weight 1.5 instead of 2).
* Gram lemmas for flip sequences `c = δ_0 + Σ_{p∈P}(δ_{p+1} - δ_p)` (`cP`), i.e. for the
  relation `1 + (g-1)Σ_{p∈P} g^p = 0`: all cross inner products are `≤ 0`, so
  `Σ c^2 t^n ≤ 1 + (1+t)S` (`gram_c`) and `Σ e^2 t^n ≤ 4 + t + (4+t+t^2)S` (`gram_f`),
  `t = θ^2 ≤ 2`, `S = Σ_P t^p`.
* `flips_engine`: `q^2 ≤ (1 + t/4 + (1+t/4+t^2/4)S + (1+(1+t)S)/r)^r` for `P ⊆ [1, r-3]`.
* `wrap_engine`: the same with one extra flip at `p = r-2` (wrapped cluster).

Standard in spirit (discrete Szegő / one-step prediction filter before Hadamard); a reusable
tool.
-/

namespace CollatzSearch.NormFilter
open Matrix Finset CollatzSearch.NormDet CollatzSearch.NormSparse

/-- Coefficients of `(2 + z) P(z)` reduced mod `z^r = 2`, where `P = Σ_{n<r} c_n z^n`. -/
def efil (r : ℕ) (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 2 * c 0 + 2 * c (r - 1) else 2 * c n + c (n - 1)

/-- The circulant index `n(i,j) = (i - j) mod r`. -/
def nn (r i j : ℕ) : ℕ := if j ≤ i then i - j else i + r - j

theorem nn_lt {r : ℕ} (i j : Fin r) : nn r i j < r := by
  have := i.2; have := j.2; unfold nn; split_ifs <;> omega

/-- Entries of the conjugated circulant. -/
theorem N_entry {r : ℕ} (c : ℕ → ℤ) {θ : ℝ} (hθ : 0 < θ) (hθr : θ ^ r = 2) (i j : Fin r) :
    θ ^ (i:ℕ) * ((circ r c i j : ℤ) : ℝ) * (θ ^ (j:ℕ))⁻¹ =
      (c (nn r i j) : ℝ) * θ ^ (nn r i j) := by
  have hi := i.2; have hj := j.2
  have hm : nn r i j ∈ range r := mem_range.mpr (nn_lt i j)
  have hc : circ r c i j = c (nn r i j) * Sh r (nn r i j) i j := by
    simp only [circ, of_apply]
    rw [sum_eq_single_of_mem (nn r i j) hm]
    intro b hb hb'; rw [Sh_eq_zero i j (mem_range.mp hb) hb']; ring
  have hθj : θ ^ (j:ℕ) ≠ 0 := pow_ne_zero _ hθ.ne'
  rw [hc, Sh_apply]
  unfold nn
  by_cases h : (j:ℕ) ≤ i
  · rw [if_pos h, if_pos (by omega)]
    have : θ ^ (i:ℕ) = θ ^ ((i:ℕ) - j) * θ ^ (j:ℕ) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp; push_cast; ring
  · rw [if_neg h, if_neg (by omega), if_pos (by omega)]
    have : θ ^ ((i:ℕ) + r - j) * θ ^ (j:ℕ) = θ ^ (i:ℕ) * 2 := by
      rw [← pow_add, ← hθr, ← pow_add]; congr 1; omega
    field_simp; push_cast; linear_combination (-(c ((i:ℕ) + r - j) : ℝ)) * this

/-- Column sums of the conjugated circulant: every column has squared norm `Σ c_n^2 θ^{2n}`. -/
theorem col_frob {r : ℕ} (c : ℕ → ℤ) {θ : ℝ} (hθ : 0 < θ) (hθr : θ ^ r = 2) (j : Fin r) :
    ∑ i : Fin r, (θ ^ (i:ℕ) * ((circ r c i j : ℤ) : ℝ) * (θ ^ (j:ℕ))⁻¹) ^ 2 =
      ∑ n ∈ range r, ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) := by
  set e : ℝ := (θ ^ (j:ℕ))⁻¹ with he
  have hej : e ^ 2 * (θ ^ (j:ℕ)) ^ 2 = 1 := by
    simp only [he]; rw [← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ hθ.ne'), one_pow]
  have : ∀ i : Fin r, (θ ^ (i:ℕ) * ((circ r c i j : ℤ) : ℝ) * e) ^ 2 = e ^ 2 *
      ∑ n ∈ range r, (c n : ℝ) ^ 2 * ((θ ^ (i:ℕ)) ^ 2 * ((Sh r n i j : ℤ) : ℝ) ^ 2) := by
    intro i
    rw [mul_pow, mul_pow]
    have hc := congrArg (fun z : ℤ => (z : ℝ)) (circ_sq c i j)
    push_cast at hc
    rw [hc, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _; ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n hn
  rw [col_sum (le_of_lt (mem_range.mp hn)) θ hθr j]
  calc e ^ 2 * ((c n : ℝ) ^ 2 * (θ ^ ((j:ℕ) + n)) ^ 2)
      = (c n : ℝ) ^ 2 * θ ^ (2 * n) * (e ^ 2 * (θ ^ (j:ℕ)) ^ 2) := by
        rw [pow_add, pow_mul]; ring
    _ = _ := by rw [hej, mul_one]

/-- `q ≤ |det circ(c)|`, hence `q^2 ≤ det^2` (extracted from `sparse_engine`). -/
theorem q_sq_le_det_sq {q r : ℕ} (hq1 : 1 < q) (hr : 0 < r) (c : ℕ → ℤ) (hc0 : Odd (c 0))
    (g : ZMod q) (hg : g ^ r = 2) (h : ∑ n ∈ range r, (c n : ZMod q) * g ^ n = 0) :
    (q : ℝ) ^ 2 ≤ ((circ r c).det : ℝ) ^ 2 := by
  set M := circ r c with hM
  have hdvd : (q:ℤ) ∣ M.det := by
    apply dvd_det_of_vecMul M (fun i : Fin r => g ^ (i:ℕ)) ⟨0, hr⟩ (by simp)
    funext j
    have hS : ∀ n ∈ range r, ∑ i : Fin r, g ^ (i:ℕ) * ((Sh r n i j : ℤ) : ZMod q) =
        g ^ n * g ^ (j:ℕ) := by
      intro n hn
      have := congrFun (vecMul_Sh (le_of_lt (mem_range.mp hn)) g hg) j
      simpa [vecMul, dotProduct] using this
    simp only [vecMul, dotProduct, map_apply, hM, circ, of_apply, Pi.zero_apply]
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ n ∈ range r, ∑ i : Fin r, g ^ (i:ℕ) * ((c n : ZMod q) * ((Sh r n i j : ℤ) : ZMod q))
        = ∑ n ∈ range r, (c n : ZMod q) * (g ^ n * g ^ (j:ℕ)) := by
          apply Finset.sum_congr rfl; intro n hn
          rw [← hS n hn, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
      _ = (∑ n ∈ range r, (c n : ZMod q) * g ^ n) * g ^ (j:ℕ) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro n _; ring
      _ = 0 := by rw [h, zero_mul]
  have hodd : Odd M.det := by
    apply det_odd_of_parity
    · intro i j hij
      have hij' : (i:ℕ) < j := hij
      simp only [hM, circ, of_apply]
      apply Finset.dvd_sum; intro n hn
      apply Dvd.dvd.mul_left
      rw [Sh_apply]; split_ifs <;> omega
    · intro i
      simp only [hM, circ, of_apply]
      rw [sum_eq_single_of_mem 0 (mem_range.mpr hr)]
      · rw [Sh_apply]; simpa using hc0
      · intro b hb hb0
        rw [Sh_apply]; have := mem_range.mp hb
        split_ifs <;> omega
  have hne : M.det ≠ 0 := by
    intro h0; rw [h0] at hodd; exact absurd hodd (by decide)
  have hle : (q:ℤ) ≤ |M.det| := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  have : (q:ℤ) ^ 2 ≤ M.det ^ 2 := by
    rw [← sq_abs M.det]; exact pow_le_pow_left₀ (by positivity) hle 2
  exact_mod_cast this

/-- **Filtered sparse engine.** -/
theorem filter_engine {q r : ℕ} (hq1 : 1 < q) (hr : 2 ≤ r) (c : ℕ → ℤ) (hc0 : Odd (c 0))
    (g : ZMod q) (hg : g ^ r = 2) (h : ∑ n ∈ range r, (c n : ZMod q) * g ^ n = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 * (r:ℝ) ^ r ≤ (((r:ℝ) - 1) * (∑ n ∈ range r, ((efil r c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)) / 4
        + ∑ n ∈ range r, ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)) ^ r := by
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
  have hNij : ∀ i j, N i j = θ ^ (i:ℕ) * ((circ r c i j : ℤ) : ℝ) * (θ ^ (j:ℕ))⁻¹ := by
    intro i j; simp [hN, hM, hd, he, diagonal_mul, mul_diagonal]
  -- the unitriangular filter
  set U : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j =>
    if i = j then 1 else if (i:ℕ) = j + 1 then θ / 2 else 0 with hU
  have hUdet : U.det = 1 := by
    rw [det_of_isLowerTriangular]
    · apply Finset.prod_eq_one; intro i _; simp [hU]
    · intro i j hij
      have : (i:ℕ) < j := hij
      simp only [hU, of_apply]
      rw [if_neg (by intro h; rw [h] at this; omega), if_neg (by omega)]
  have hdet : (N * U).det = (M.det : ℝ) := by rw [det_mul, hUdet, mul_one, hNdet]
  set jl : Fin r := ⟨r - 1, by omega⟩ with hjl
  -- entries of N U
  have hNU : ∀ i j, (N * U) i j = N i j + if h : (j:ℕ) + 1 < r then θ / 2 * N i ⟨j + 1, h⟩ else 0 := by
    intro i j
    rw [mul_apply]
    have : ∀ k, N i k * U k j = (if k = j then N i j else 0) +
        (if (k:ℕ) = j + 1 then θ / 2 * N i k else 0) := by
      intro k
      simp only [hU, of_apply]
      by_cases hkj : k = j
      · subst hkj; simp
      · rw [if_neg hkj, if_neg hkj]; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => this k, sum_add_distrib, sum_ite_eq' univ j]
    simp only [mem_univ, if_true]
    congr 1
    split_ifs with hj1
    · rw [sum_eq_single_of_mem (⟨j + 1, hj1⟩ : Fin r) (mem_univ _)]
      · simp
      · intro b _ hb; rw [if_neg]; intro h; apply hb; ext; simpa using h
    · apply sum_eq_zero; intro k _; rw [if_neg]; have := k.2; omega
  -- filtered columns
  have hcolj : ∀ j : Fin r, j ≠ jl → ∀ i : Fin r,
      (N * U) i j = (1/2) * (θ ^ (i:ℕ) * ((circ r (efil r c) i j : ℤ) : ℝ) * (θ ^ (j:ℕ))⁻¹) := by
    intro j hj i
    have hj1 : (j:ℕ) + 1 < r := by
      have : (j:ℕ) ≠ r - 1 := fun h => hj (Fin.ext h)
      have := j.2; omega
    rw [hNU, dif_pos hj1, hNij, hNij, N_entry c hθ hθr, N_entry c hθ hθr, N_entry (efil r c) hθ hθr]
    have hi := i.2
    have hn' : nn r (i:ℕ) ((⟨(j:ℕ) + 1, hj1⟩ : Fin r) : ℕ) =
        if nn r i j = 0 then r - 1 else nn r i j - 1 := by
      change nn r (i:ℕ) ((j:ℕ) + 1) = _; unfold nn; split_ifs <;> omega
    rw [hn']
    have hlt := nn_lt i j
    unfold efil
    by_cases h0 : nn r i j = 0
    · rw [if_pos h0, if_pos h0, h0]
      have e4 : θ * θ ^ (r - 1) = 2 := by rw [← pow_succ']; rw [← hθr]; congr 1; omega
      push_cast
      linear_combination ((c (r - 1) : ℝ) / 2) * e4
    · rw [if_neg h0, if_neg h0]
      have e2 : θ ^ (nn r i j) = θ * θ ^ (nn r i j - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e2]; push_cast; ring
  have hlast : ∀ i : Fin r, (N * U) i jl = N i jl := by
    intro i; rw [hNU, dif_neg (by simp [hjl]; omega), add_zero]
  -- Frobenius
  set E := ∑ n ∈ range r, ((efil r c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) with hE
  set Q := ∑ n ∈ range r, ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) with hQ
  have hcol : ∀ j : Fin r, ∑ i, (N * U) i j ^ 2 = E / 4 + if j = jl then Q - E / 4 else 0 := by
    intro j
    by_cases hj : j = jl
    · rw [if_pos hj]; subst hj
      simp_rw [hlast, hNij]; rw [col_frob c hθ hθr]; ring
    · rw [if_neg hj]
      simp_rw [hcolj j hj]
      have := col_frob (efil r c) hθ hθr j
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      simp_rw [← mul_pow]; rw [this]; ring
  have hfrob : ∑ i, ∑ j, (N * U) i j ^ 2 = ((r:ℝ) - 1) * E / 4 + Q := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hcol j, sum_add_distrib,
      sum_ite_eq' univ jl]
    simp; ring
  have hH := det_sq_mul_le_real (N * U)
  rw [hfrob, hdet] at hH
  have hrr : (0:ℝ) ≤ (r:ℝ) ^ r := by positivity
  calc (q:ℝ) ^ 2 * (r:ℝ) ^ r ≤ ((M.det : ℤ) : ℝ) ^ 2 * (r:ℝ) ^ r := mul_le_mul_of_nonneg_right hsq hrr
    _ ≤ _ := by simpa [Fintype.card_fin] using hH


/-- **Normalised filtered engine (T1').** `q^2 ≤ (Q' + Q/r)^r` with `Q' = ¼ Σ e_n^2 θ^{2n}`,
`Q = Σ c_n^2 θ^{2n}`. -/
theorem filter_engine' {q r : ℕ} (hq1 : 1 < q) (hr : 2 ≤ r) (c : ℕ → ℤ) (hc0 : Odd (c 0))
    (g : ZMod q) (hg : g ^ r = 2) (h : ∑ n ∈ range r, (c n : ZMod q) * g ^ n = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 ≤ ((∑ n ∈ range r, ((efil r c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)) / 4
        + (∑ n ∈ range r, ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)) / r) ^ r := by
  have H := filter_engine hq1 hr c hc0 g hg h θ hθ hθr
  set E := ∑ n ∈ range r, ((efil r c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)
  set Q := ∑ n ∈ range r, ((c n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)
  have hE : 0 ≤ E := sum_nonneg fun n _ => by positivity
  have hQ : 0 ≤ Q := sum_nonneg fun n _ => by positivity
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h1 : ((r:ℝ) - 1) * E / 4 + Q ≤ (r:ℝ) * (E / 4 + Q / r) := by
    rw [mul_add, mul_div_cancel₀ _ hr0.ne']; nlinarith
  have h2 : (((r:ℝ) - 1) * E / 4 + Q) ^ r ≤ ((r:ℝ) * (E / 4 + Q / r)) ^ r :=
    pow_le_pow_left₀ (by have : (1:ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
                         nlinarith) h1 r
  rw [mul_pow] at h2
  have hrr : (0:ℝ) < (r:ℝ) ^ r := by positivity
  have := H.trans h2
  nlinarith

/-! ## Flip sequences and the Gram lemma -/

/-- `c = δ_0 + Σ_{p∈P} (δ_{p+1} - δ_p)`: coefficients of `1 + (z-1) Σ_{p∈P} z^p`. -/
def cP (P : Finset ℕ) (n : ℕ) : ℤ := ind 0 n + ∑ p ∈ P, (ind (p + 1) n - ind p n)

/-- `f = 2δ_0 + δ_1 + Σ_{p∈P} (δ_{p+2} + δ_{p+1} - 2δ_p)`: coefficients of `(2+z) c`. -/
def fP (P : Finset ℕ) (n : ℕ) : ℤ :=
  2 * ind 0 n + ind 1 n + ∑ p ∈ P, (ind (p + 2) n + ind (p + 1) n - 2 * ind p n)

theorem sum_mul_ind {r b : ℕ} (hb : b < r) (F : ℕ → ℝ) :
    ∑ n ∈ range r, F n * ((ind b n : ℤ) : ℝ) = F b := by
  simp [ind, hb]

theorem sq_add_sum (s : Finset ℕ) (u v w : ℕ → ℝ) :
    ∑ n ∈ s, (u n + v n) ^ 2 * w n =
      ∑ n ∈ s, u n ^ 2 * w n + 2 * ∑ n ∈ s, u n * v n * w n + ∑ n ∈ s, v n ^ 2 * w n := by
  rw [Finset.mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro n _; ring

theorem cP_insert {P : Finset ℕ} {a : ℕ} (ha : a ∉ P) (n : ℕ) :
    cP (insert a P) n = cP P n + (ind (a + 1) n - ind a n) := by
  simp only [cP, sum_insert ha]; ring

theorem fP_insert {P : Finset ℕ} {a : ℕ} (ha : a ∉ P) (n : ℕ) :
    fP (insert a P) n = fP P n + (ind (a + 2) n + ind (a + 1) n - 2 * ind a n) := by
  simp only [fP, sum_insert ha]; ring

/-- Gram bound for `c`: `Σ c_n^2 θ^{2n} ≤ 1 + (1+θ^2) Σ_P θ^{2p}` (all cross terms `≤ 0`). -/
theorem gram_c {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ : 0 < θ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r) :
    ∑ n ∈ range r, ((cP P n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) ≤
      1 + (1 + θ ^ 2) * ∑ p ∈ P, θ ^ (2 * p) := by
  induction P using Finset.induction_on_max with
  | empty =>
    have : ∀ n, ((cP ∅ n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) = θ ^ (2 * n) * ((ind 0 n : ℤ) : ℝ) := by
      intro n; simp only [cP, sum_empty, add_zero]; unfold ind; split_ifs <;> simp
    rw [sum_congr rfl fun n _ => this n, sum_mul_ind (by omega)]; simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have hPa := hP a (mem_insert_self _ _)
    have ih' := ih fun p hp => hP p (mem_insert_of_mem hp)
    set u : ℕ → ℝ := fun n => ((cP s n : ℤ) : ℝ) with hu
    set v : ℕ → ℝ := fun n => ((ind (a + 1) n : ℤ) : ℝ) - ((ind a n : ℤ) : ℝ) with hv
    set w : ℕ → ℝ := fun n => θ ^ (2 * n) with hw
    have hsplit : ∑ n ∈ range r, ((cP (insert a s) n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
        ∑ n ∈ range r, (u n + v n) ^ 2 * w n := by
      apply sum_congr rfl; intro n _; simp only [hu, hv, hw, cP_insert has]; push_cast; ring
    have hvv : ∑ n ∈ range r, v n ^ 2 * w n = θ ^ (2 * (a + 1)) + θ ^ (2 * a) := by
      have : ∀ n, v n ^ 2 * w n = w n * ((ind (a + 1) n : ℤ) : ℝ) + w n * ((ind a n : ℤ) : ℝ) := by
        intro n
        have hz : (ind (a + 1) n - ind a n) ^ 2 = ind (a + 1) n + ind a n := by
          unfold ind; split_ifs <;> first | omega | norm_num
        have hz' : (((ind (a + 1) n : ℤ) : ℝ) - ((ind a n : ℤ) : ℝ)) ^ 2 =
            ((ind (a + 1) n : ℤ) : ℝ) + ((ind a n : ℤ) : ℝ) := by exact_mod_cast hz
        simp only [hv]; rw [hz']; ring
      rw [sum_congr rfl fun n _ => this n, sum_add_distrib, sum_mul_ind (by omega),
        sum_mul_ind (by omega)]
    have huv : ∑ n ∈ range r, u n * v n * w n = u (a + 1) * w (a + 1) - u a * w a := by
      have : ∀ n, u n * v n * w n = (u n * w n) * ((ind (a + 1) n : ℤ) : ℝ) -
          (u n * w n) * ((ind a n : ℤ) : ℝ) := by intro n; simp only [hv]; ring
      rw [sum_congr rfl fun n _ => this n, sum_sub_distrib, sum_mul_ind (F := fun n => u n * w n)
        (by omega), sum_mul_ind (F := fun n => u n * w n) (by omega)]
    have hu1 : u (a + 1) = 0 := by
      simp only [hu, cP]
      have : ∑ p ∈ s, (ind (p + 1) (a + 1) - ind p (a + 1)) = 0 := by
        apply sum_eq_zero; intro x hx; have := hlt x hx; unfold ind; split_ifs <;> omega
      rw [this]; unfold ind; split_ifs <;> first | omega | simp_all
    have hu0 : 0 ≤ u a := by
      simp only [hu, cP]
      have : 0 ≤ ind 0 a + ∑ p ∈ s, (ind (p + 1) a - ind p a) := by
        apply add_nonneg
        · unfold ind; split_ifs <;> omega
        · apply sum_nonneg; intro x hx; have := hlt x hx; unfold ind; split_ifs <;> omega
      exact_mod_cast this
    rw [hsplit, sq_add_sum, hvv, huv, hu1, sum_insert has]
    have hwa : 0 ≤ w a := by positivity
    have e1 : θ ^ (2 * (a + 1)) = θ ^ 2 * θ ^ (2 * a) := by rw [← pow_add]; congr 1; ring
    rw [e1]
    have : 0 ≤ u a * w a := mul_nonneg hu0 hwa
    simp only [hw] at this ⊢
    nlinarith

/-- Gram bound for `e = (2+z)c`: `Σ f_n^2 θ^{2n} ≤ 4 + θ^2 + (4 + θ^2 + θ^4) Σ_P θ^{2p}`
(cross terms `≤ 0` as `θ^2 ≤ 2`). -/
theorem gram_f {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ : 0 < θ) (ht2 : θ ^ 2 ≤ 2) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r) :
    ∑ n ∈ range r, ((fP P n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) ≤
      4 + θ ^ 2 + (4 + θ ^ 2 + θ ^ 4) * ∑ p ∈ P, θ ^ (2 * p) := by
  induction P using Finset.induction_on_max with
  | empty =>
    have : ∀ n, ((fP ∅ n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
        4 * (θ ^ (2 * n) * ((ind 0 n : ℤ) : ℝ)) + θ ^ (2 * n) * ((ind 1 n : ℤ) : ℝ) := by
      intro n; simp only [fP, sum_empty, add_zero]; unfold ind; split_ifs <;> first | omega | (norm_num <;> simp_all)
    rw [sum_congr rfl fun n _ => this n, sum_add_distrib, ← Finset.mul_sum,
      sum_mul_ind (F := fun n => θ ^ (2 * n)) (by omega),
      sum_mul_ind (F := fun n => θ ^ (2 * n)) (by omega)]
    simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have hPa := hP a (mem_insert_self _ _)
    have ih' := ih fun p hp => hP p (mem_insert_of_mem hp)
    set u : ℕ → ℝ := fun n => ((fP s n : ℤ) : ℝ) with hu
    set v : ℕ → ℝ := fun n => ((ind (a + 2) n : ℤ) : ℝ) + ((ind (a + 1) n : ℤ) : ℝ) -
      2 * ((ind a n : ℤ) : ℝ) with hv
    set w : ℕ → ℝ := fun n => θ ^ (2 * n) with hw
    have hsplit : ∑ n ∈ range r, ((fP (insert a s) n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
        ∑ n ∈ range r, (u n + v n) ^ 2 * w n := by
      apply sum_congr rfl; intro n _; simp only [hu, hv, hw, fP_insert has]; push_cast; ring
    have hvv : ∑ n ∈ range r, v n ^ 2 * w n =
        θ ^ (2 * (a + 2)) + θ ^ (2 * (a + 1)) + 4 * θ ^ (2 * a) := by
      have : ∀ n, v n ^ 2 * w n = w n * ((ind (a + 2) n : ℤ) : ℝ) +
          w n * ((ind (a + 1) n : ℤ) : ℝ) + 4 * (w n * ((ind a n : ℤ) : ℝ)) := by
        intro n
        have hz : (ind (a + 2) n + ind (a + 1) n - 2 * ind a n) ^ 2 =
            ind (a + 2) n + ind (a + 1) n + 4 * ind a n := by
          unfold ind; split_ifs <;> first | omega | norm_num
        have hz' : (((ind (a + 2) n : ℤ) : ℝ) + ((ind (a + 1) n : ℤ) : ℝ) -
            2 * ((ind a n : ℤ) : ℝ)) ^ 2 =
            ((ind (a + 2) n : ℤ) : ℝ) + ((ind (a + 1) n : ℤ) : ℝ) + 4 * ((ind a n : ℤ) : ℝ) := by
          exact_mod_cast hz
        simp only [hv]; rw [hz']; ring
      rw [sum_congr rfl fun n _ => this n, sum_add_distrib, sum_add_distrib, ← Finset.mul_sum,
        sum_mul_ind (b := a + 2) (show a + 2 < r by omega),
        sum_mul_ind (b := a + 1) (show a + 1 < r by omega), sum_mul_ind (b := a) (show a < r by omega)]
    have huv : ∑ n ∈ range r, u n * v n * w n =
        u (a + 2) * w (a + 2) + u (a + 1) * w (a + 1) - 2 * (u a * w a) := by
      have : ∀ n, u n * v n * w n = (u n * w n) * ((ind (a + 2) n : ℤ) : ℝ) +
          (u n * w n) * ((ind (a + 1) n : ℤ) : ℝ) - 2 * ((u n * w n) * ((ind a n : ℤ) : ℝ)) := by
        intro n; simp only [hv]; ring
      rw [sum_congr rfl fun n _ => this n, sum_sub_distrib, sum_add_distrib, ← Finset.mul_sum,
        sum_mul_ind (F := fun n => u n * w n) (show a + 2 < r by omega),
        sum_mul_ind (F := fun n => u n * w n) (show a + 1 < r by omega),
        sum_mul_ind (F := fun n => u n * w n) (show a < r by omega)]
    have hu2 : u (a + 2) = 0 := by
      simp only [hu, fP]
      have : ∑ p ∈ s, (ind (p + 2) (a + 2) + ind (p + 1) (a + 2) - 2 * ind p (a + 2)) = 0 := by
        apply sum_eq_zero; intro x hx; have := hlt x hx; unfold ind; split_ifs <;> omega
      rw [this]; unfold ind; split_ifs <;> first | omega | simp_all
    have hu1 : 0 ≤ u (a + 1) := by
      simp only [hu, fP]
      have : 0 ≤ 2 * ind 0 (a + 1) + ind 1 (a + 1) +
          ∑ p ∈ s, (ind (p + 2) (a + 1) + ind (p + 1) (a + 1) - 2 * ind p (a + 1)) := by
        apply add_nonneg
        · unfold ind; split_ifs <;> omega
        · apply sum_nonneg; intro x hx; have := hlt x hx; unfold ind; split_ifs <;> omega
      exact_mod_cast this
    have hu10 : u (a + 1) ≤ u a := by
      simp only [hu, fP]
      have : 2 * ind 0 (a + 1) + ind 1 (a + 1) +
          ∑ p ∈ s, (ind (p + 2) (a + 1) + ind (p + 1) (a + 1) - 2 * ind p (a + 1)) ≤
          2 * ind 0 a + ind 1 a + ∑ p ∈ s, (ind (p + 2) a + ind (p + 1) a - 2 * ind p a) := by
        apply add_le_add
        · unfold ind; split_ifs <;> (try simp_all) <;> omega
        · apply sum_le_sum; intro x hx; have := hlt x hx; unfold ind; split_ifs <;> omega
      exact_mod_cast this
    rw [hsplit, sq_add_sum, hvv, huv, hu2, sum_insert has]
    have hwa : 0 ≤ w a := by positivity
    have e1 : θ ^ (2 * (a + 1)) = θ ^ 2 * θ ^ (2 * a) := by rw [← pow_add]; congr 1; ring
    have e2 : θ ^ (2 * (a + 2)) = θ ^ 4 * θ ^ (2 * a) := by rw [← pow_add]; congr 1; ring
    simp only [hw] at hwa ⊢
    rw [e1, e2]
    have k1 : θ ^ 2 * u (a + 1) ≤ 2 * u a := by nlinarith [mul_le_mul_of_nonneg_right ht2 hu1]
    have k2 : 0 ≤ (2 * u a - θ ^ 2 * u (a + 1)) * θ ^ (2 * a) := mul_nonneg (by linarith) hwa
    nlinarith


theorem ind_pred {a n : ℕ} (h : 1 ≤ n) : ind a (n - 1) = ind (a + 1) n := by
  unfold ind; split_ifs <;> omega

theorem cP_zero {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) : cP P 0 = 1 := by
  unfold cP
  rw [sum_eq_zero]
  · simp [ind]
  · intro p hp; have := hP p hp
    rw [show ind (p + 1) 0 = 0 from if_neg (by omega), show ind p 0 = 0 from if_neg (by omega)]
    norm_num

theorem cP_top {r : ℕ} (hr : 2 ≤ r) {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r) :
    cP P (r - 1) = 0 := by
  unfold cP
  rw [sum_eq_zero]
  · unfold ind; split_ifs <;> omega
  · intro p hp; have := hP p hp; unfold ind; split_ifs <;> omega

/-- `efil` of a flip sequence is the explicit `fP`. -/
theorem efil_cP {r : ℕ} (hr : 2 ≤ r) {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r)
    {n : ℕ} (hn : n < r) : efil r (cP P) n = fP P n := by
  unfold efil
  split_ifs with h0
  · subst h0
    rw [cP_zero (fun p hp => (hP p hp).1), cP_top hr hP]
    unfold fP
    rw [sum_eq_zero]
    · simp [ind]
    · intro p hp; have := hP p hp
      rw [show ind (p + 2) 0 = 0 from if_neg (by omega), show ind (p + 1) 0 = 0 from if_neg (by omega),
        show ind p 0 = 0 from if_neg (by omega)]
      norm_num
  · have h1 : 1 ≤ n := by omega
    unfold cP fP
    simp only [ind_pred h1, zero_add]
    have key : ∀ x, ind (x + 2) n + ind (x + 1) n - 2 * ind x n =
        2 * (ind (x + 1) n - ind x n) + (ind (x + 1 + 1) n - ind (x + 1) n) := by intro x; ring
    simp only [key, sum_add_distrib, ← Finset.mul_sum]; ring

/-- The flip sequence realises `1 + (g-1) Σ_{p∈P} g^p`. -/
theorem rel_cP {q r : ℕ} (hr : 0 < r) (g : ZMod q) {P : Finset ℕ} (hP : ∀ p ∈ P, p + 1 < r) :
    ∑ n ∈ range r, ((cP P n : ℤ) : ZMod q) * g ^ n = 1 + (g - 1) * ∑ p ∈ P, g ^ p := by
  unfold cP
  push_cast
  simp only [add_mul, sum_add_distrib, sum_ind_g hr, pow_zero]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply sum_congr rfl; intro p hp
  have := hP p hp
  simp only [sub_mul, sum_sub_distrib, sum_ind_g this, sum_ind_g (show p < r by omega)]
  ring

/-- **Flip engine.** If `1 + (g-1) Σ_{p∈P} g^p = 0` in `ZMod q` (`g^r = 2`) with every
`p ∈ [1, r-3]`, then with `t = θ^2`, `S = Σ_P t^p`:
`q^2 ≤ (1 + t/4 + (1 + t/4 + t^2/4) S + (1 + (1+t) S)/r)^r`. -/
theorem flips_engine {q r : ℕ} (hq1 : 1 < q) (hr : 2 ≤ r) (g : ZMod q) (hg : g ^ r = 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r) (h : 1 + (g - 1) * ∑ p ∈ P, g ^ p = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) (ht2 : θ ^ 2 ≤ 2) :
    (q : ℝ) ^ 2 ≤ (1 + θ ^ 2 / 4 + (1 + θ ^ 2 / 4 + θ ^ 4 / 4) * ∑ p ∈ P, θ ^ (2 * p)
      + (1 + (1 + θ ^ 2) * ∑ p ∈ P, θ ^ (2 * p)) / r) ^ r := by
  have hc0 : Odd (cP P 0) := by rw [cP_zero (fun p hp => (hP p hp).1)]; decide
  have hrel : ∑ n ∈ range r, ((cP P n : ℤ) : ZMod q) * g ^ n = 0 := by
    rw [rel_cP (by omega) g (fun p hp => by have := hP p hp; omega), h]
  have H := filter_engine' hq1 hr (cP P) hc0 g hg hrel θ hθ hθr
  have hE : ∑ n ∈ range r, ((efil r (cP P) n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      ∑ n ∈ range r, ((fP P n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) :=
    sum_congr rfl fun n hn => by rw [efil_cP hr hP (mem_range.mp hn)]
  rw [hE] at H
  have gf := gram_f hr hθ ht2 P hP
  have gc := gram_c hr hθ P hP
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  refine H.trans (pow_le_pow_left₀ (by positivity) ?_ r)
  have h1 := div_le_div_of_nonneg_right gc hr0.le
  have : (∑ n ∈ range r, ((fP P n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n)) / 4 ≤
      1 + θ ^ 2 / 4 + (1 + θ ^ 2 / 4 + θ ^ 4 / 4) * ∑ p ∈ P, θ ^ (2 * p) := by linarith
  linarith

/-! ## The wrap variant: one flip at `p = r - 2` -/

/-- `c + δ_{r-1} - δ_{r-2}`. -/
def cW (r : ℕ) (P : Finset ℕ) (n : ℕ) : ℤ := cP P n + (ind (r - 1) n - ind (r - 2) n)

theorem efil_cW {r : ℕ} (hr : 4 ≤ r) {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r)
    {n : ℕ} (hn : n < r) :
    efil r (cW r P) n = fP P n + (2 * ind 0 n + ind (r - 1) n - 2 * ind (r - 2) n) := by
  rw [← efil_cP (by omega) hP hn]
  unfold efil cW
  split_ifs with h0
  · subst h0; unfold ind; split_ifs <;> omega
  · have h1 : 1 ≤ n := by omega
    rw [ind_pred h1, ind_pred h1]
    unfold ind; split_ifs <;> omega

theorem gram_cW {r : ℕ} (hr : 4 ≤ r) {θ : ℝ} (hθ : 0 < θ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r) :
    ∑ n ∈ range r, ((cW r P n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) ≤
      1 + (1 + θ ^ 2) * ∑ p ∈ P, θ ^ (2 * p) + θ ^ (2 * (r - 1)) + θ ^ (2 * (r - 2)) := by
  set u : ℕ → ℝ := fun n => ((cP P n : ℤ) : ℝ) with hu
  set v : ℕ → ℝ := fun n => ((ind (r - 1) n : ℤ) : ℝ) - ((ind (r - 2) n : ℤ) : ℝ) with hv
  set w : ℕ → ℝ := fun n => θ ^ (2 * n) with hw
  have hsplit : ∑ n ∈ range r, ((cW r P n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      ∑ n ∈ range r, (u n + v n) ^ 2 * w n := by
    apply sum_congr rfl; intro n _; simp only [hu, hv, hw, cW]; push_cast; ring
  have hvv : ∑ n ∈ range r, v n ^ 2 * w n = θ ^ (2 * (r - 1)) + θ ^ (2 * (r - 2)) := by
    have : ∀ n, v n ^ 2 * w n = w n * ((ind (r - 1) n : ℤ) : ℝ) + w n * ((ind (r - 2) n : ℤ) : ℝ) := by
      intro n
      have hz : (ind (r - 1) n - ind (r - 2) n) ^ 2 = ind (r - 1) n + ind (r - 2) n := by
        unfold ind; split_ifs <;> first | omega | norm_num
      have hz' : (((ind (r - 1) n : ℤ) : ℝ) - ((ind (r - 2) n : ℤ) : ℝ)) ^ 2 =
          ((ind (r - 1) n : ℤ) : ℝ) + ((ind (r - 2) n : ℤ) : ℝ) := by exact_mod_cast hz
      simp only [hv]; rw [hz']; ring
    rw [sum_congr rfl fun n _ => this n, sum_add_distrib,
      sum_mul_ind (b := r - 1) (show r - 1 < r by omega),
      sum_mul_ind (b := r - 2) (show r - 2 < r by omega)]
  have huv : ∑ n ∈ range r, u n * v n * w n = u (r - 1) * w (r - 1) - u (r - 2) * w (r - 2) := by
    have : ∀ n, u n * v n * w n = (u n * w n) * ((ind (r - 1) n : ℤ) : ℝ) -
        (u n * w n) * ((ind (r - 2) n : ℤ) : ℝ) := by intro n; simp only [hv]; ring
    rw [sum_congr rfl fun n _ => this n, sum_sub_distrib,
      sum_mul_ind (F := fun n => u n * w n) (show r - 1 < r by omega),
      sum_mul_ind (F := fun n => u n * w n) (show r - 2 < r by omega)]
  have hu1 : u (r - 1) = 0 := by
    simp only [hu]; rw [cP_top (by omega) hP]; simp
  have hu0 : 0 ≤ u (r - 2) := by
    simp only [hu, cP]
    have : 0 ≤ ind 0 (r - 2) + ∑ p ∈ P, (ind (p + 1) (r - 2) - ind p (r - 2)) := by
      apply add_nonneg
      · unfold ind; split_ifs <;> omega
      · apply sum_nonneg; intro x hx; have := hP x hx; unfold ind; split_ifs <;> omega
    exact_mod_cast this
  rw [hsplit, sq_add_sum, hvv, huv, hu1]
  have gc := gram_c (by omega) hθ P hP
  have : 0 ≤ u (r - 2) * w (r - 2) := mul_nonneg hu0 (by positivity)
  simp only [hw, hu] at this gc ⊢
  nlinarith

theorem gram_fW {r : ℕ} (hr : 4 ≤ r) {θ : ℝ} (hθ : 0 < θ) (ht2 : θ ^ 2 ≤ 2) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r) :
    ∑ n ∈ range r, ((efil r (cW r P) n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) ≤
      16 + θ ^ 2 + (4 + θ ^ 2 + θ ^ 4) * ∑ p ∈ P, θ ^ (2 * p) + θ ^ (2 * (r - 1))
        + 4 * θ ^ (2 * (r - 2)) := by
  set u : ℕ → ℝ := fun n => ((fP P n : ℤ) : ℝ) with hu
  set v : ℕ → ℝ := fun n => 2 * ((ind 0 n : ℤ) : ℝ) + ((ind (r - 1) n : ℤ) : ℝ) -
    2 * ((ind (r - 2) n : ℤ) : ℝ) with hv
  set w : ℕ → ℝ := fun n => θ ^ (2 * n) with hw
  have hsplit : ∑ n ∈ range r, ((efil r (cW r P) n : ℤ) : ℝ) ^ 2 * θ ^ (2 * n) =
      ∑ n ∈ range r, (u n + v n) ^ 2 * w n := by
    apply sum_congr rfl; intro n hn
    rw [efil_cW hr hP (mem_range.mp hn)]; simp only [hu, hv, hw]; push_cast; ring
  have hvv : ∑ n ∈ range r, v n ^ 2 * w n = 4 + θ ^ (2 * (r - 1)) + 4 * θ ^ (2 * (r - 2)) := by
    have : ∀ n, v n ^ 2 * w n = 4 * (w n * ((ind 0 n : ℤ) : ℝ)) +
        w n * ((ind (r - 1) n : ℤ) : ℝ) + 4 * (w n * ((ind (r - 2) n : ℤ) : ℝ)) := by
      intro n
      have hz : (2 * ind 0 n + ind (r - 1) n - 2 * ind (r - 2) n) ^ 2 =
          4 * ind 0 n + ind (r - 1) n + 4 * ind (r - 2) n := by
        unfold ind; split_ifs <;> omega
      have hz' : (2 * ((ind 0 n : ℤ) : ℝ) + ((ind (r - 1) n : ℤ) : ℝ) -
          2 * ((ind (r - 2) n : ℤ) : ℝ)) ^ 2 =
          4 * ((ind 0 n : ℤ) : ℝ) + ((ind (r - 1) n : ℤ) : ℝ) + 4 * ((ind (r - 2) n : ℤ) : ℝ) := by
        exact_mod_cast hz
      simp only [hv]; rw [hz']; ring
    rw [sum_congr rfl fun n _ => this n, sum_add_distrib, sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_mul_ind (b := 0) (show 0 < r by omega),
      sum_mul_ind (b := r - 1) (show r - 1 < r by omega),
      sum_mul_ind (b := r - 2) (show r - 2 < r by omega)]
    simp [hw]
  have huv : ∑ n ∈ range r, u n * v n * w n =
      2 * (u 0 * w 0) + u (r - 1) * w (r - 1) - 2 * (u (r - 2) * w (r - 2)) := by
    have : ∀ n, u n * v n * w n = 2 * ((u n * w n) * ((ind 0 n : ℤ) : ℝ)) +
        (u n * w n) * ((ind (r - 1) n : ℤ) : ℝ) - 2 * ((u n * w n) * ((ind (r - 2) n : ℤ) : ℝ)) := by
      intro n; simp only [hv]; ring
    rw [sum_congr rfl fun n _ => this n, sum_sub_distrib, sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum,
      sum_mul_ind (F := fun n => u n * w n) (show 0 < r by omega),
      sum_mul_ind (F := fun n => u n * w n) (show r - 1 < r by omega),
      sum_mul_ind (F := fun n => u n * w n) (show r - 2 < r by omega)]
  have hu00 : u 0 = 2 := by
    simp only [hu]; rw [← efil_cP (by omega) hP (show 0 < r by omega)]
    unfold efil; rw [if_pos rfl, cP_zero (fun p hp => (hP p hp).1), cP_top (by omega) hP]; norm_num
  have hu1 : 0 ≤ u (r - 1) := by
    simp only [hu, fP]
    have : 0 ≤ 2 * ind 0 (r - 1) + ind 1 (r - 1) +
        ∑ p ∈ P, (ind (p + 2) (r - 1) + ind (p + 1) (r - 1) - 2 * ind p (r - 1)) := by
      apply add_nonneg
      · unfold ind; split_ifs <;> omega
      · apply sum_nonneg; intro x hx; have := hP x hx; unfold ind; split_ifs <;> omega
    exact_mod_cast this
  have hu10 : u (r - 1) ≤ u (r - 2) := by
    simp only [hu, fP]
    have : 2 * ind 0 (r - 1) + ind 1 (r - 1) +
        ∑ p ∈ P, (ind (p + 2) (r - 1) + ind (p + 1) (r - 1) - 2 * ind p (r - 1)) ≤
        2 * ind 0 (r - 2) + ind 1 (r - 2) +
        ∑ p ∈ P, (ind (p + 2) (r - 2) + ind (p + 1) (r - 2) - 2 * ind p (r - 2)) := by
      apply add_le_add
      · unfold ind; split_ifs <;> omega
      · apply sum_le_sum; intro x hx; have := hP x hx; unfold ind; split_ifs <;> omega
    exact_mod_cast this
  rw [hsplit, sq_add_sum, hvv, huv, hu00]
  have gf := gram_f (by omega) hθ ht2 P hP
  have hwa : 0 ≤ θ ^ (2 * (r - 2)) := by positivity
  have e1 : θ ^ (2 * (r - 1)) = θ ^ 2 * θ ^ (2 * (r - 2)) := by rw [← pow_add]; congr 1; omega
  have k1 : θ ^ 2 * u (r - 1) ≤ 2 * u (r - 2) := by nlinarith [mul_le_mul_of_nonneg_right ht2 hu1]
  have k2 : 0 ≤ (2 * u (r - 2) - θ ^ 2 * u (r - 1)) * θ ^ (2 * (r - 2)) := mul_nonneg (by linarith) hwa
  simp only [hw, hu] at gf k1 k2 ⊢
  rw [e1] at ⊢
  simp only [pow_zero, mul_one, mul_zero]
  nlinarith

/-- **Wrap flip engine.** If `1 + (g-1)(Σ_{p∈P} g^p + g^{r-2}) = 0` with `P ⊆ [1, r-3]`, then
`q^2 ≤ (E/4 + Q/r)^r` with the explicit Gram bounds. -/
theorem wrap_engine {q r : ℕ} (hq1 : 1 < q) (hr : 4 ≤ r) (g : ZMod q) (hg : g ^ r = 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r)
    (h : 1 + (g - 1) * (∑ p ∈ P, g ^ p + g ^ (r - 2)) = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) (ht2 : θ ^ 2 ≤ 2) :
    (q : ℝ) ^ 2 ≤ ((16 + θ ^ 2 + (4 + θ ^ 2 + θ ^ 4) * ∑ p ∈ P, θ ^ (2 * p) + θ ^ (2 * (r - 1))
        + 4 * θ ^ (2 * (r - 2))) / 4 + (1 + (1 + θ ^ 2) * ∑ p ∈ P, θ ^ (2 * p)
        + θ ^ (2 * (r - 1)) + θ ^ (2 * (r - 2))) / r) ^ r := by
  have hc0 : Odd (cW r P 0) := by
    unfold cW; rw [cP_zero (fun p hp => (hP p hp).1)]
    rw [show ind (r - 1) 0 = 0 from if_neg (by omega), show ind (r - 2) 0 = 0 from if_neg (by omega)]
    decide
  have hrel : ∑ n ∈ range r, ((cW r P n : ℤ) : ZMod q) * g ^ n = 0 := by
    unfold cW; push_cast
    simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib]
    have := rel_cP (q := q) (r := r) (P := P) (by omega) g (fun p hp => by have := hP p hp; omega)
    rw [this, sum_ind_g (show r - 1 < r by omega), sum_ind_g (show r - 2 < r by omega)]
    have e : g ^ (r - 1) = g * g ^ (r - 2) := by rw [← pow_succ']; congr 1; omega
    rw [e]; linear_combination h
  have H := filter_engine' hq1 (by omega) (cW r P) hc0 g hg hrel θ hθ hθr
  have gf := gram_fW hr hθ ht2 P hP
  have gc := gram_cW hr hθ P hP
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  refine H.trans (pow_le_pow_left₀ (by positivity) ?_ r)
  have h1 := div_le_div_of_nonneg_right gc hr0.le
  have h2 := div_le_div_of_nonneg_right gf (show (0:ℝ) ≤ 4 by norm_num)
  linarith

end CollatzSearch.NormFilter

#print axioms CollatzSearch.NormFilter.filter_engine
#print axioms CollatzSearch.NormFilter.filter_engine'
#print axioms CollatzSearch.NormFilter.flips_engine
#print axioms CollatzSearch.NormFilter.wrap_engine
