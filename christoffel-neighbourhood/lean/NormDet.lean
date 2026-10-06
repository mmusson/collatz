import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# integer transfer by the adjugate, odd determinants, Frobenius AM–GM

* `dvd_det_of_vecMul`: if an integer matrix `M` has a row vector `v` over `ZMod q` with a
  coordinate `1` and `v · M = 0`, then `q ∣ det M` (adjugate).
* `Sh r n`: the `r × r` shift by `n` with weight `2` on wrapped entries; `vecMul_Sh`: the row
  `(g^i)` is a left eigenvector with eigenvalue `g^n` whenever `g^r = 2`.
* `det_three_odd`: `det (Sh a - Sh b + 1)` is odd for `1 ≤ a, b < r`.
* `det_sq_mul_le`: `det(M)^2 · n^n ≤ (Σ M_ij^2)^n` (AM–GM on eigenvalues of `MᵀM`).
* `frob_three`: `Σ (Sh a - Sh b + 1)_ij^2 = 3r + 3a + 3b` for distinct `1 ≤ a, b < r`.
* `le_det_three`, `le_typeI`, `le_typeII`: if `g ∈ ZMod q` (`q > 1`) has `g^r = 2` and
  `g^a - g^b + 1 = 0`, then `q^2 r^r ≤ (3r + 3a + 3b)^r`; specialised to the trinomials
  `g^(p+1) - g^p + 1` and `g^e - g + 1`.
-/

namespace CollatzSearch.NormDet
open Matrix Finset

theorem dvd_det_of_vecMul {n q : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ZMod q)
    (i0 : Fin n) (hv : v i0 = 1) (h : vecMul v (M.map (Int.cast : ℤ → ZMod q)) = 0) :
    (q : ℤ) ∣ M.det := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_det]
  set N := M.map (Int.cast : ℤ → ZMod q)
  have key : vecMul v (N * N.adjugate) = N.det • v := by
    rw [Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul] at key
  have := congrFun key i0
  simp [hv] at this
  exact this.symm

/-- If every entry above the diagonal is even and every diagonal entry is odd, the
determinant is odd. -/
theorem det_odd_of_parity {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hup : ∀ i j, i < j → 2 ∣ M i j) (hdiag : ∀ i, Odd (M i i)) : Odd M.det := by
  rw [← ZMod.intCast_eq_one_iff_odd, Int.cast_det,
    det_of_isLowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simpa [ZMod.intCast_eq_one_iff_odd] using hdiag i
  · intro i j hij
    simp only [map_apply]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hup i j hij


/-- Column sum through the support of a weighted shift. -/
theorem sum_col {R : Type*} [AddCommMonoid R] {r n j : ℕ} (hj : j < r) (hn : n ≤ r)
    (F H : ℕ → R) :
    ∑ i : Fin r, (if (i:ℕ) = j + n then F i else if (i:ℕ) + r = j + n then H i else 0) =
      if j + n < r then F (j + n) else H (j + n - r) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if i = j + n then F i else if i + r = j + n then H i else 0) r]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem (j + n) (by simp [h])]
    · simp
    · intro b _ hb
      rw [if_neg hb, if_neg (by omega)]
  · rw [Finset.sum_eq_single_of_mem (j + n - r) (by simp; omega)]
    · rw [if_neg (by omega), if_pos (by omega)]
    · intro b hb hb'
      simp at hb
      rw [if_neg (by omega), if_neg (by omega)]

/-- The weighted shift: `1` at `(j+n, j)`, `2` at `(j+n-r, j)` when that wraps. -/
def Sh (r n : ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => if (i:ℕ) = j + n then 1 else if (i:ℕ) + r = j + n then 2 else 0

theorem vecMul_Sh {R : Type*} [CommRing R] {r n : ℕ} (hn : n ≤ r) (g : R) (hg : g ^ r = 2) :
    vecMul (fun i : Fin r => g ^ (i:ℕ)) ((Sh r n).map (Int.cast : ℤ → R)) =
      fun i : Fin r => g ^ n * g ^ (i:ℕ) := by
  funext j
  simp only [vecMul, dotProduct, map_apply, Sh, of_apply]
  have : ∀ i : Fin r, g ^ (i:ℕ) * ((if (i:ℕ) = j + n then (1:ℤ) else
      if (i:ℕ) + r = j + n then 2 else 0 : ℤ) : R) =
      (if (i:ℕ) = j + n then g ^ (i:ℕ) else if (i:ℕ) + r = j + n then 2 * g ^ (i:ℕ) else 0) := by
    intro i; split_ifs <;> simp [mul_comm]
  simp_rw [this]
  rw [sum_col j.2 hn (fun i => g ^ i) (fun i => 2 * g ^ i)]
  split_ifs with h
  · ring
  · rw [← hg, ← pow_add, ← pow_add]; congr 1; omega

theorem Sh_apply (r n : ℕ) (i j : Fin r) :
    Sh r n i j = if (i:ℕ) = j + n then 1 else if (i:ℕ) + r = j + n then 2 else 0 := rfl

theorem Sh_mul_Sh {r a b : ℕ} (ha : a < r) (hb : b < r) (hab : a ≠ b) (i j : Fin r) :
    Sh r a i j * Sh r b i j = 0 := by
  rw [Sh_apply, Sh_apply]
  split_ifs <;> first | omega | simp

theorem Sh_mul_one {r a : ℕ} (ha : 1 ≤ a) (ha' : a < r) (i j : Fin r) :
    Sh r a i j * (1 : Matrix (Fin r) (Fin r) ℤ) i j = 0 := by
  rw [Sh_apply, one_apply]
  by_cases h : i = j
  · subst h; simp; omega
  · simp [h]

theorem sum_Sh_sq {r n : ℕ} (hn : n ≤ r) :
    ∑ i : Fin r, ∑ j : Fin r, (Sh r n i j) ^ 2 = r + 3 * n := by
  rw [Finset.sum_comm]
  have hcol : ∀ j : Fin r, ∑ i : Fin r, (Sh r n i j) ^ 2 = if (j:ℕ) + n < r then 1 else 4 := by
    intro j
    have : ∀ i : Fin r, (Sh r n i j) ^ 2 =
        (if (i:ℕ) = j + n then (fun _ => (1:ℤ)) i else
          if (i:ℕ) + r = j + n then (fun _ => (4:ℤ)) i else 0) := by
      intro i; rw [Sh_apply]; split_ifs <;> norm_num
    exact (Finset.sum_congr rfl fun i _ => this i).trans (sum_col (R := ℤ) j.2 hn (fun _ => (1:ℤ)) (fun _ => (4:ℤ)))
  simp_rw [hcol]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j + n < r then (1:ℤ) else 4) r]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + n := ⟨r - n, by omega⟩
  rw [Finset.sum_range_add]
  rw [Finset.sum_congr rfl (fun x hx => if_pos (by simp at hx; omega)),
    Finset.sum_congr rfl (fun x hx => if_neg (by simp at hx; omega))]
  simp; ring

theorem sum_one_sq (r : ℕ) :
    ∑ i : Fin r, ∑ j : Fin r, ((1 : Matrix (Fin r) (Fin r) ℤ) i j) ^ 2 = r := by
  simp [one_apply]

/-- Frobenius norm of `Sh a - Sh b + 1`. -/
theorem frob_three {r a b : ℕ} (ha : 1 ≤ a) (ha' : a < r) (hb : 1 ≤ b) (hb' : b < r)
    (hab : a ≠ b) :
    ∑ i : Fin r, ∑ j : Fin r, ((Sh r a - Sh r b + 1) i j) ^ 2 = 3 * r + 3 * a + 3 * b := by
  have : ∀ i j : Fin r, ((Sh r a - Sh r b + 1) i j) ^ 2 =
      (Sh r a i j) ^ 2 + (Sh r b i j) ^ 2 + ((1 : Matrix (Fin r) (Fin r) ℤ) i j) ^ 2 := by
    intro i j
    rw [Matrix.add_apply, Matrix.sub_apply]
    have h1 := Sh_mul_Sh ha' hb' hab i j
    have h2 := Sh_mul_one ha ha' i j
    have h3 := Sh_mul_one hb hb' i j
    linear_combination (-2) * h1 + 2 * h2 - 2 * h3
  simp_rw [this, Finset.sum_add_distrib]
  rw [sum_Sh_sq ha'.le, sum_Sh_sq hb'.le, sum_one_sq]
  ring

theorem vecMul_three {R : Type*} [CommRing R] {r a b : ℕ} (ha : a ≤ r) (hb : b ≤ r) (g : R)
    (hg : g ^ r = 2) :
    vecMul (fun i : Fin r => g ^ (i:ℕ)) ((Sh r a - Sh r b + 1).map (Int.cast : ℤ → R)) =
      fun i : Fin r => (g ^ a - g ^ b + 1) * g ^ (i:ℕ) := by
  rw [Matrix.map_add _ (Int.cast_add (R := R)), Matrix.map_sub _ (Int.cast_sub (R := R)), Matrix.map_one (Int.cast : ℤ → R) Int.cast_zero Int.cast_one,
    vecMul_add, vecMul_sub, vecMul_one, vecMul_Sh ha g hg, vecMul_Sh hb g hg]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem det_three_odd {r a b : ℕ} (ha : 1 ≤ a) (ha' : a < r) (hb : 1 ≤ b) (hb' : b < r) :
    Odd (Sh r a - Sh r b + 1).det := by
  apply det_odd_of_parity
  · intro i j hij
    have hij' : (i:ℕ) < j := hij
    rw [Matrix.add_apply, Matrix.sub_apply, Sh_apply, Sh_apply, one_apply, if_neg (ne_of_lt hij)]
    split_ifs <;> first | omega | norm_num
  · intro i
    rw [Matrix.add_apply, Matrix.sub_apply, Sh_apply, Sh_apply, one_apply, if_pos rfl]
    split_ifs <;> first | omega | norm_num

theorem amgm_prod {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∏ i, x i) * (n:ℝ) ^ n ≤ (∑ i, x i) ^ n := by
  have h := Real.geom_mean_le_arith_mean_weighted (univ : Finset (Fin n)) (fun _ => (n:ℝ)⁻¹) x
    (fun _ _ => by positivity) (by simp; field_simp) (fun i _ => hx i)
  have h2 := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx i) _) h n
  rw [← Finset.prod_pow] at h2
  simp_rw [Real.rpow_inv_natCast_pow (hx _) (by omega : n ≠ 0)] at h2
  rw [← Finset.mul_sum, mul_pow] at h2
  have hn' : (0:ℝ) < (n:ℝ) ^ n := by positivity
  calc (∏ i, x i) * (n:ℝ) ^ n ≤ ((n:ℝ)⁻¹ ^ n * (∑ i, x i) ^ n) * (n:ℝ) ^ n :=
        mul_le_mul_of_nonneg_right h2 hn'.le
    _ = (∑ i, x i) ^ n := by
        rw [inv_pow]; field_simp

/-- **Frobenius AM–GM (Hadamard-type) bound.** `det(M)^2 · n^n ≤ (Σ M_ij^2)^n`. -/
theorem det_sq_mul_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    M.det ^ 2 * (n:ℤ) ^ n ≤ (∑ i, ∑ j, M i j ^ 2) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  suffices h : ((M.det : ℝ)) ^ 2 * (n:ℝ) ^ n ≤ (∑ i, ∑ j, (M i j : ℝ) ^ 2) ^ n by
    exact_mod_cast h
  set N : Matrix (Fin n) (Fin n) ℝ := M.map (Int.cast : ℤ → ℝ) with hN
  have hH := isHermitian_conjTranspose_mul_self N
  have hdet : (Nᴴ * N).det = (M.det : ℝ) ^ 2 := by
    rw [det_mul, det_conjTranspose, hN, ← Int.cast_det]; simp [sq]
  have htr : (Nᴴ * N).trace = ∑ i, ∑ j, (M i j : ℝ) ^ 2 := by
    simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply, star_trivial, hN, map_apply]
    rw [Finset.sum_comm]; simp [sq]
  have h1 := hH.det_eq_prod_eigenvalues
  have h2 := hH.trace_eq_sum_eigenvalues
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => eigenvalues_conjTranspose_mul_self_nonneg N i
  rw [← hdet, ← htr, h1, h2]
  simpa using amgm_prod hn _ hnn


/-- **Packaged engine.** -/
theorem le_det_three {q r a b : ℕ} (hq1 : 1 < q) (ha : 1 ≤ a) (ha' : a < r) (hb : 1 ≤ b)
    (hb' : b < r) (hab : a ≠ b) (g : ZMod q) (hg : g ^ r = 2) (h : g ^ a - g ^ b + 1 = 0) :
    (q:ℤ) ^ 2 * (r:ℤ) ^ r ≤ (3 * r + 3 * a + 3 * b : ℤ) ^ r := by
  set M := Sh r a - Sh r b + 1 with hM
  have hr : 0 < r := by omega
  have hdvd : (q:ℤ) ∣ M.det := by
    apply dvd_det_of_vecMul M (fun i : Fin r => g ^ (i:ℕ)) ⟨0, hr⟩ (by simp)
    rw [hM, vecMul_three ha'.le hb'.le g hg]
    funext i; simp [h]
  have hodd := det_three_odd (r := r) ha ha' hb hb'
  have hne : M.det ≠ 0 := by
    intro h0; rw [← hM, h0] at hodd; exact absurd hodd (by decide)
  have hle : (q:ℤ) ≤ |M.det| := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  have hsq : (q:ℤ) ^ 2 ≤ M.det ^ 2 := by
    rw [← sq_abs M.det]; exact pow_le_pow_left₀ (by positivity) hle 2
  have hD := det_sq_mul_le M
  rw [hM, frob_three ha ha' hb hb' hab] at hD
  rw [← hM] at hD
  push_cast at hD
  calc (q:ℤ) ^ 2 * (r:ℤ) ^ r ≤ M.det ^ 2 * (r:ℤ) ^ r :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ _ := hD

/-- Type I engine: `g^(p+1) - g^p + 1 = 0` ⇒ `q^2 r^r ≤ (3r + 6p + 3)^r`. -/
theorem le_typeI {q r p : ℕ} (hq1 : 1 < q) (hp : 1 ≤ p) (hpr : p + 1 < r) (g : ZMod q)
    (hg : g ^ r = 2) (h : g ^ (p + 1) - g ^ p + 1 = 0) :
    (q:ℤ) ^ 2 * (r:ℤ) ^ r ≤ (3 * r + 6 * p + 3 : ℤ) ^ r := by
  have := le_det_three hq1 (by omega) hpr hp (by omega) (by omega) g hg h
  push_cast at this
  convert this using 2; ring

/-- Type II engine: `g^e - g + 1 = 0` ⇒ `q^2 r^r ≤ (3r + 3e + 3)^r`. -/
theorem le_typeII {q r e : ℕ} (hq1 : 1 < q) (he : 2 ≤ e) (her : e < r) (g : ZMod q)
    (hg : g ^ r = 2) (h : g ^ e - g + 1 = 0) :
    (q:ℤ) ^ 2 * (r:ℤ) ^ r ≤ (3 * r + 3 * e + 3 : ℤ) ^ r := by
  have := le_det_three hq1 (by omega) her (le_refl 1) (by omega) (by omega) g hg (by simpa using h)
  push_cast at this
  convert this using 2

end CollatzSearch.NormDet

#print axioms CollatzSearch.NormDet.dvd_det_of_vecMul
#print axioms CollatzSearch.NormDet.det_sq_mul_le
#print axioms CollatzSearch.NormDet.le_det_three
#print axioms CollatzSearch.NormDet.le_typeI
#print axioms CollatzSearch.NormDet.le_typeII

