import NormDet

/-!
# the sparse norm engine (weighted Hadamard bound)

* `sparse_engine`: if `g ∈ ZMod q` (`q > 1`) has `g^r = 2`, `c : ℕ → ℤ` has `c 0` odd and
  `Σ_{n<r} c_n g^n = 0`, and `θ > 0` with `θ^r = 2`, then `q^2 ≤ (Σ_{n<r} c_n^2 θ^{2n})^r`.
  Proof: the matrix `M = Σ c_n Sh(r,n)` (circulant with wrapped entries doubled) has the left
  null vector `(g^i)` mod `q`, so `q ∣ det M`; `det M` is odd (diagonal `c_0`, even entries
  above the diagonal); conjugating by `diag(θ^i)` makes every entry `c_n θ^n`, so the
  Frobenius norm is `r Q` and AM–GM on the eigenvalues of `NᵀN` gives `det^2 ≤ Q^r`.
  This strictly improves the `NormMain` integer Frobenius bound (`(3r+3a+3b)/r` vs `1+θ^{2a}+θ^{2b}`).
* `engine3`, `engine5`: the trinomial `1 - g^a + g^b` and the five-term
  `1 - g^a + g^b - g^c + g^e` specialisations.
-/

namespace CollatzSearch.NormSparse
open Matrix Finset CollatzSearch.NormDet

/-- Real Hadamard / Frobenius AM–GM: `det(N)^2 · n^n ≤ (Σ N_ij^2)^n`. -/
theorem det_sq_mul_le_real {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) :
    N.det ^ 2 * (n:ℝ) ^ n ≤ (∑ i, ∑ j, N i j ^ 2) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hH := isHermitian_conjTranspose_mul_self N
  have hdet : (Nᴴ * N).det = N.det ^ 2 := by
    rw [det_mul, det_conjTranspose]; simp [sq]
  have htr : (Nᴴ * N).trace = ∑ i, ∑ j, N i j ^ 2 := by
    simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply, star_trivial]
    rw [Finset.sum_comm]; simp [sq]
  have h1 := hH.det_eq_prod_eigenvalues
  have h2 := hH.trace_eq_sum_eigenvalues
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => eigenvalues_conjTranspose_mul_self_nonneg N i
  rw [← hdet, ← htr, h1, h2]
  simpa using amgm_prod hn _ hnn

/-- The circulant-type matrix `Σ_n c_n Sh(r,n)`. -/
def circ (r : ℕ) (c : ℕ → ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => ∑ n ∈ range r, c n * Sh r n i j

theorem Sh_eq_zero {r n : ℕ} (i j : Fin r) (hn : n < r)
    (hne : n ≠ (if (j:ℕ) ≤ i then (i:ℕ) - j else (i:ℕ) + r - j)) : Sh r n i j = 0 := by
  have := i.2; have := j.2
  rw [Sh_apply]; split_ifs at hne ⊢ <;> omega

theorem circ_sq {r : ℕ} (c : ℕ → ℤ) (i j : Fin r) :
    (circ r c i j) ^ 2 = ∑ n ∈ range r, c n ^ 2 * Sh r n i j ^ 2 := by
  have hi := i.2; have hj := j.2
  set n0 := (if (j:ℕ) ≤ i then (i:ℕ) - j else (i:ℕ) + r - j) with hn0
  have hn0r : n0 < r := by rw [hn0]; split_ifs <;> omega
  have hm : n0 ∈ range r := mem_range.mpr hn0r
  simp only [circ, of_apply]
  rw [sum_eq_single_of_mem n0 hm, sum_eq_single_of_mem n0 hm]
  · ring
  · intro b hb hb'; rw [Sh_eq_zero i j (mem_range.mp hb) hb']; ring
  · intro b hb hb'; rw [Sh_eq_zero i j (mem_range.mp hb) hb']; ring

theorem col_sum {r n : ℕ} (hn : n ≤ r) (θ : ℝ) (hθr : θ ^ r = 2) (j : Fin r) :
    ∑ i : Fin r, (θ ^ (i:ℕ)) ^ 2 * ((Sh r n i j : ℤ) : ℝ) ^ 2 = (θ ^ ((j:ℕ) + n)) ^ 2 := by
  have : ∀ i : Fin r, (θ ^ (i:ℕ)) ^ 2 * ((Sh r n i j : ℤ) : ℝ) ^ 2 =
      (if (i:ℕ) = j + n then (fun k : ℕ => (θ ^ k) ^ 2) i else
        if (i:ℕ) + r = j + n then (fun k : ℕ => 4 * (θ ^ k) ^ 2) i else 0) := by
    intro i; rw [Sh_apply]; split_ifs <;> push_cast <;> ring
  rw [(Finset.sum_congr rfl fun i _ => this i).trans
    (sum_col (R := ℝ) j.2 hn (fun k : ℕ => (θ ^ k) ^ 2) (fun k : ℕ => 4 * (θ ^ k) ^ 2))]
  split_ifs with h
  · rfl
  · show 4 * (θ ^ ((j:ℕ) + n - r)) ^ 2 = _
    have e2 : θ ^ ((j:ℕ) + n) = 2 * θ ^ ((j:ℕ) + n - r) := by
      rw [← hθr, ← pow_add]; congr 1; omega
    rw [e2]; ring

/-- **Sparse norm engine (weighted Hadamard).** If `g ∈ ZMod q` (`q > 1`) has
`g^r = 2`, the integer sequence `c` has `c_0` odd and `Σ_{n<r} c_n g^n = 0`, and `θ > 0` with
`θ^r = 2`, then `q^2 ≤ (Σ_{n<r} c_n^2 θ^{2n})^r`. -/
theorem sparse_engine {q r : ℕ} (hq1 : 1 < q) (hr : 0 < r) (c : ℕ → ℤ) (hc0 : Odd (c 0))
    (g : ZMod q) (hg : g ^ r = 2) (h : ∑ n ∈ range r, (c n : ZMod q) * g ^ n = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 ≤ (∑ n ∈ range r, (c n : ℝ) ^ 2 * θ ^ (2 * n)) ^ r := by
  set M := circ r c with hM
  -- divisibility
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
  -- odd determinant
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
  have hsq : (q:ℝ) ^ 2 ≤ (M.det : ℝ) ^ 2 := by
    have : (q:ℤ) ^ 2 ≤ M.det ^ 2 := by
      rw [← sq_abs M.det]; exact pow_le_pow_left₀ (by positivity) hle 2
    exact_mod_cast this
  -- conjugated real matrix
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
  have hNij : ∀ i j, N i j = d i * (M i j : ℝ) * e j := by
    intro i j; simp [hN, diagonal_mul, mul_diagonal]
  have hfrob : ∑ i, ∑ j, N i j ^ 2 = r * ∑ n ∈ range r, (c n : ℝ) ^ 2 * θ ^ (2 * n) := by
    rw [Finset.sum_comm]
    have hcol : ∀ j : Fin r, ∑ i : Fin r, N i j ^ 2 =
        ∑ n ∈ range r, (c n : ℝ) ^ 2 * θ ^ (2 * n) := by
      intro j
      have hej : (e j) ^ 2 * (θ ^ (j:ℕ)) ^ 2 = 1 := by
        simp only [he]; rw [← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ hθ.ne'), one_pow]
      have : ∀ i : Fin r, N i j ^ 2 = (e j) ^ 2 *
          ∑ n ∈ range r, (c n : ℝ) ^ 2 * ((θ ^ (i:ℕ)) ^ 2 * ((Sh r n i j : ℤ) : ℝ) ^ 2) := by
        intro i
        rw [hNij, mul_pow, mul_pow]
        have hc := congrArg (fun z : ℤ => (z : ℝ)) (circ_sq c i j)
        simp only [hM] at hc ⊢
        push_cast at hc
        rw [hc, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _; simp only [hd]; ring
      rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n hn
      rw [col_sum (le_of_lt (mem_range.mp hn)) θ hθr j]
      calc (e j) ^ 2 * ((c n : ℝ) ^ 2 * (θ ^ ((j:ℕ) + n)) ^ 2)
          = (c n : ℝ) ^ 2 * θ ^ (2 * n) * ((e j) ^ 2 * (θ ^ (j:ℕ)) ^ 2) := by
            rw [pow_add, pow_mul]; ring
        _ = _ := by rw [hej, mul_one]
    rw [Finset.sum_congr rfl fun j _ => hcol j]
    simp
  have hH := det_sq_mul_le_real N
  rw [hfrob, hNdet, mul_pow] at hH
  have hrr : (0:ℝ) < (r:ℝ) ^ r := by positivity
  have : (M.det : ℝ) ^ 2 ≤ (∑ n ∈ range r, (c n : ℝ) ^ 2 * θ ^ (2 * n)) ^ r := by
    by_contra hc
    push Not at hc
    nlinarith
  linarith

/-- `θ = 2^{1/r}` exists. -/
theorem exists_theta {r : ℕ} (hr : 0 < r) : ∃ θ : ℝ, 0 < θ ∧ θ ^ r = 2 :=
  ⟨(2:ℝ) ^ ((r:ℝ)⁻¹), by positivity, Real.rpow_inv_natCast_pow (by norm_num) (by omega)⟩

/-- Indicator of `n = a`. -/
def ind (a n : ℕ) : ℤ := if n = a then 1 else 0

theorem sum_ind_g {q r a : ℕ} (ha : a < r) (g : ZMod q) :
    ∑ n ∈ range r, ((ind a n : ℤ) : ZMod q) * g ^ n = g ^ a := by
  simp [ind, ha]

theorem sum_ind_θ {r a : ℕ} (ha : a < r) (θ : ℝ) :
    ∑ n ∈ range r, ((ind a n : ℤ) : ℝ) * θ ^ (2 * n) = θ ^ (2 * a) := by
  simp [ind, ha]

/-- **Trinomial engine.** `1 - g^a + g^b = 0` (`0 < a, b < r`, `a ≠ b`) ⇒
`q^2 ≤ (1 + θ^{2a} + θ^{2b})^r`. -/
theorem engine3 {q r a b : ℕ} (hq1 : 1 < q) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (har : a < r) (hbr : b < r) (g : ZMod q) (hg : g ^ r = 2) (h : 1 - g ^ a + g ^ b = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 ≤ (1 + θ ^ (2 * a) + θ ^ (2 * b)) ^ r := by
  have hr : 0 < r := by omega
  set c : ℕ → ℤ := fun n => ind 0 n - ind a n + ind b n with hc
  have hrel : ∑ n ∈ range r, (c n : ZMod q) * g ^ n = 0 := by
    simp only [hc]; push_cast
    simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, sum_ind_g hr, sum_ind_g har,
      sum_ind_g hbr]
    simpa using h
  have hc0 : Odd (c 0) := by
    simp [hc, ind, ha.ne, hb.ne]
  have hsq : ∀ n, ((c n : ℤ) : ℝ) ^ 2 = (ind 0 n : ℝ) + ind a n + ind b n := by
    intro n
    have : (c n) ^ 2 = ind 0 n + ind a n + ind b n := by
      simp only [hc, ind]; split_ifs <;> omega
    exact_mod_cast this
  have := sparse_engine hq1 hr c hc0 g hg hrel θ hθ hθr
  simp only [hsq, add_mul, sum_add_distrib, sum_ind_θ hr, sum_ind_θ har, sum_ind_θ hbr] at this
  simpa using this

/-- **Five-term engine.** `1 - g^a + g^b - g^c + g^e = 0` with `0, a, b, c, e < r` distinct ⇒
`q^2 ≤ (1 + θ^{2a} + θ^{2b} + θ^{2c} + θ^{2e})^r`. -/
theorem engine5 {q r a b c e : ℕ} (hq1 : 1 < q) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hce : c < e) (her : e < r) (g : ZMod q) (hg : g ^ r = 2)
    (h : 1 - g ^ a + g ^ b - g ^ c + g ^ e = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    (q : ℝ) ^ 2 ≤ (1 + θ ^ (2 * a) + θ ^ (2 * b) + θ ^ (2 * c) + θ ^ (2 * e)) ^ r := by
  have hr : 0 < r := by omega
  set f : ℕ → ℤ := fun n => ind 0 n - ind a n + ind b n - ind c n + ind e n with hf
  have hrel : ∑ n ∈ range r, (f n : ZMod q) * g ^ n = 0 := by
    simp only [hf]; push_cast
    simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, sum_ind_g hr,
      sum_ind_g (show a < r by omega), sum_ind_g (show b < r by omega),
      sum_ind_g (show c < r by omega), sum_ind_g her]
    simpa using h
  have hc0 : Odd (f 0) := by
    simp [hf, ind, ha.ne, show 0 ≠ b by omega, show 0 ≠ c by omega, show 0 ≠ e by omega]
  have hsq : ∀ n, ((f n : ℤ) : ℝ) ^ 2 =
      (ind 0 n : ℝ) + ind a n + ind b n + ind c n + ind e n := by
    intro n
    have : (f n) ^ 2 = ind 0 n + ind a n + ind b n + ind c n + ind e n := by
      simp only [hf, ind]; split_ifs <;> omega
    exact_mod_cast this
  have := sparse_engine hq1 hr f hc0 g hg hrel θ hθ hθr
  simp only [hsq, add_mul, sum_add_distrib, sum_ind_θ hr, sum_ind_θ (show a < r by omega),
    sum_ind_θ (show b < r by omega), sum_ind_θ (show c < r by omega), sum_ind_θ her] at this
  simpa using this

end CollatzSearch.NormSparse

#print axioms CollatzSearch.NormSparse.sparse_engine
#print axioms CollatzSearch.NormSparse.engine3
#print axioms CollatzSearch.NormSparse.engine5
