import NormCofactor

/-!
# window theorem for `gcd(A, r) ≥ 2`

* `Bnum_front`: `B_{r+1}(v) = 3^r + 2^{v 0} B_r(v ∘ succ)`; `Bnum_odd`; `Bnum_inj`: the
  Böhm–Sontacchi numerator is injective on words with entries `≥ 1` (equal `B` ⇒ equal partial
  sums), by 2-adic valuation and front induction.
* **T3** `no_cycle_window_noncoprime`: for `d = gcd(A, r) ≥ 2`, any word (entries `≥ 1`) whose
  partial sums differ from those of `chr r A` (somewhere) only inside a window `[k, k+w)`, by at
  most `h`, with `(w 2^{2h+1})^r 2^{(w-1)A} < 2^{(A - A/d) r}`, has `(2^A - 3^r) ∤ B`. The
  cofactor `S_d ≥ U^{d-1}` divides `X = (B(v) - B(chr))/(3^{r-k-w} 2^m)`, which is nonzero and
  `< U^{d-1}` in absolute value. Max window (exact check): `(r,A) = (60,96)`, `d = 12`: `w ≤ 50`
  (`h = 1`), `48` (`h = 3`); `(106,170)`, `d = 2`: `48` (`h = 1`),
  `46` (`h = 3`); `(2326,3688)`, `d = 2`: `1155` (`h = 1`), `1153` (`h = 3`). Exponentially many words
  in `w`; covers height-one interval bridges up to that length when `d ≥ 2`.
* `cycle_window_noncoprime`: cycle form.

Word-level, needs `d ≥ 2`; credit Solomon Prop. 6.3 (one-move cofactor argument).
-/

namespace Collatz.NormWindow
open Collatz.NormGoal Collatz.NormReduce Collatz.NormAll
  Collatz.NormCofactor Finset

theorem psum_front (v : ℕ → ℕ) (j : ℕ) : psum v (j + 1) = v 0 + psum (fun i => v (i + 1)) j := by
  unfold psum; rw [sum_range_succ']; ring

/-- Front decomposition `B_{r+1}(v) = 3^r + 2^{v 0} B_r(v ∘ succ)`. -/
theorem Bnum_front (r : ℕ) (v : ℕ → ℕ) :
    Bnum (r + 1) v = 3 ^ r + 2 ^ v 0 * Bnum r (fun i => v (i + 1)) := by
  unfold Bnum
  rw [sum_range_succ', mul_sum]
  simp only [psum_front]
  have h0 : psum v 0 = 0 := by simp [psum]
  rw [h0, add_comm]
  congr 1
  · simp
  · apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    rw [show r + 1 - 1 - (j + 1) = r - 1 - j by omega, pow_add]; ring

/-- `B_r(v)` is odd when `r ≥ 1` and the entries `v i`, `i + 1 < r`, are `≥ 1`. -/
theorem Bnum_odd {r : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hv : ∀ i, i + 1 < r → 1 ≤ v i) :
    Bnum r v % 2 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [Bnum_front]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Bnum]
  · have h1 := hv 0 (by omega)
    have : 2 ∣ 2 ^ v 0 := dvd_pow_self 2 (by omega)
    have h3 : 3 ^ n % 2 = 1 := by rw [Nat.pow_mod]; simp
    obtain ⟨c, hc⟩ := this
    rw [hc, mul_assoc, Nat.add_mul_mod_self_left, h3]

theorem two_adic_cancel {a b x y : ℕ} (h : 2 ^ a * x = 2 ^ b * y) (hx : x % 2 = 1)
    (hy : y % 2 = 1) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨c, rfl⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [this] at hx; simp [Nat.mul_mod, pow_succ] at hx
  · exact hab
  · obtain ⟨c, rfl⟩ : ∃ c, a = b + c + 1 := ⟨a - b - 1, by omega⟩
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [← this] at hy; simp [Nat.mul_mod, pow_succ] at hy

/-- **2-adic injectivity of the Böhm–Sontacchi numerator.** If all entries `v i, w i`
(`i + 1 < r`) are `≥ 1` and `B_r(v) = B_r(w)`, then `v` and `w` have the same partial sums
below `r`. -/
theorem Bnum_inj {r : ℕ} {v w : ℕ → ℕ} (hv : ∀ i, i + 1 < r → 1 ≤ v i)
    (hw : ∀ i, i + 1 < r → 1 ≤ w i) (h : Bnum r v = Bnum r w) :
    ∀ j < r, psum v j = psum w j := by
  induction r generalizing v w with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [Bnum_front, Bnum_front] at h
    have h' : 2 ^ v 0 * Bnum n (fun i => v (i + 1)) = 2 ^ w 0 * Bnum n (fun i => w (i + 1)) := by
      omega
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : j = 0 := by omega
      subst this; simp [psum]
    have hv' : ∀ i, i + 1 < n → 1 ≤ v (i + 1) := fun i hi => hv (i + 1) (by omega)
    have hw' : ∀ i, i + 1 < n → 1 ≤ w (i + 1) := fun i hi => hw (i + 1) (by omega)
    have h0 : v 0 = w 0 := two_adic_cancel h' (Bnum_odd hn hv') (Bnum_odd hn hw')
    rw [h0] at h'
    have hB := Nat.eq_of_mul_eq_mul_left (by positivity) h'
    rcases j with _ | j
    · simp [psum]
    · rw [psum_front, psum_front, h0, ih hv' hw' hB j (by omega)]

/-- `(a + b) / r ≤ a / r + b / r + 1`. -/
theorem div_add_le (a b r : ℕ) (hr : 0 < r) : (a + b) / r ≤ a / r + b / r + 1 := by
  rw [Nat.add_div hr]; split_ifs <;> omega


/-- `|2^x - 2^y| ≤ 2^z` for `x, y ≤ z`. -/
theorem abs_two_pow_sub_le {x y z : ℕ} (hx : x ≤ z) (hy : y ≤ z) :
    |(2 : ℤ) ^ x - 2 ^ y| ≤ 2 ^ z := by
  have h1 : (2 : ℤ) ^ x ≤ 2 ^ z := pow_le_pow_right₀ (by norm_num) hx
  have h2 : (2 : ℤ) ^ y ≤ 2 ^ z := pow_le_pow_right₀ (by norm_num) hy
  have p1 : (0 : ℤ) < 2 ^ x := by positivity
  have p2 : (0 : ℤ) < 2 ^ y := by positivity
  rw [abs_le]; constructor <;> linarith

/-- **T3: window theorem for `gcd(A, r) ≥ 2`.** Let `d = gcd(A, r) ≥ 2`,
`3^r + 1 < 2^A`, and let `v` (entries `v i ≥ 1` for `i + 1 < r`) have partial sums that agree
with those of `chr r A` outside the window `[k, k + w)`, differ from them by at most `h`
everywhere, and differ somewhere. If
`(w · 2^{2h+1})^r · 2^{(w-1)A} < 2^{(A - A/d) r}`, then `(2^A - 3^r) ∤ B(v)`.
Proof: `B` is 2-adically injective on strictly increasing partial sums (`Bnum_inj`), so
`Δ = B(v) - B(chr) ≠ 0`; Solomon's cofactor `S_d` divides `Δ = 3^{r-k-w} 2^m X`, hence `X`;
but `|X| ≤ w 2^{2h+1} max_s 3^{w-1-s} 2^{⌊sA/r⌋} < 2^{A - A/d} = U^{d-1} ≤ S_d`.
The window can be as long as about `(1 - 1/d) r`: e.g. `w ≤ 1155` at `(r, A) = (2326, 3688)`,
`h = 1`. Corollary (`d ≥ 2`): height-one interval bridges of length up to
the same bound are excluded. -/
theorem no_cycle_window_noncoprime (r A : ℕ) (hd : 2 ≤ Nat.gcd A r) (hq : 3 ^ r + 1 < 2 ^ A)
    (k w h : ℕ) (hkw : k + w ≤ r)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * A) < 2 ^ ((A - A / Nat.gcd A r) * r))
    (v : ℕ → ℕ) (hv1 : ∀ i, i + 1 < r → 1 ≤ v i)
    (hout : ∀ j < r, (j < k ∨ k + w ≤ j) → psum v j = psum (NormGoal.chr r A) j)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r A) j + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r A) j ≤ psum v j + h)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r A) j) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  have hr0 : 0 < r := by obtain ⟨j, hj, -⟩ := hne; omega
  have hAr := r_lt_A hq
  obtain ⟨r', A', hr', hA', hr'0⟩ := gcd_decomp (A := A) hr0
  set d := Nat.gcd A r with hd_def
  obtain ⟨hS1, hS2, hS3, hSq, hSB⟩ :=
    solomon_factor (d := d) (r' := r') (A' := A') hd hr'0 (by rw [← hr', ← hA']; exact hq)
  rw [← hr', ← hA'] at hSq hSB
  set S := Sg (2 ^ A') (3 ^ r') d with hSdef
  -- c and a
  have hc : ∀ j, psum (NormGoal.chr r A) j = j * A / r := fun j => psum_chr j
  -- Δ ≠ 0
  have hchr1 : ∀ i, i + 1 < r → 1 ≤ NormGoal.chr r A i := by
    intro i hi
    have : 1 ≤ A / r := (Nat.one_le_div_iff hr0).mpr hAr.le
    rcases chr_two_letter (A := A) hr0 i (by omega) with e | e <;> omega
  have hBne : Bnum r v ≠ Bnum r (NormGoal.chr r A) := by
    intro hB
    obtain ⟨j, hj, hj'⟩ := hne
    exact hj' (Bnum_inj hv1 hchr1 hB j hj)
  -- S ∣ Δ in ℤ
  have hSD : (S : ℤ) ∣ (Bnum r v : ℤ) - Bnum r (NormGoal.chr r A) :=
    dvd_sub (Int.natCast_dvd_natCast.mpr (dvd_trans hSq hdiv)) (Int.natCast_dvd_natCast.mpr hSB)
  -- window sum
  set m := psum (NormGoal.chr r A) k - h with hm
  set X : ℤ := ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
    ((2 : ℤ) ^ (psum v (k + s) - m) - 2 ^ (psum (NormGoal.chr r A) (k + s) - m)) with hX
  have hmono : ∀ s, psum (NormGoal.chr r A) k ≤ psum (NormGoal.chr r A) (k + s) := by
    intro s; rw [hc, hc]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  have hDX : (Bnum r v : ℤ) - Bnum r (NormGoal.chr r A) = 3 ^ (r - k - w) * 2 ^ m * X := by
    rw [cast_Bnum, cast_Bnum, ← sum_sub_distrib]
    have hsub : ∑ j ∈ Ico k (k + w), ((3 : ℤ) ^ (r - 1 - j) * 2 ^ psum v j -
        3 ^ (r - 1 - j) * 2 ^ psum (NormGoal.chr r A) j) =
        ∑ j ∈ range r, ((3 : ℤ) ^ (r - 1 - j) * 2 ^ psum v j -
        3 ^ (r - 1 - j) * 2 ^ psum (NormGoal.chr r A) j) := by
      apply sum_subset
      · intro j hj; rw [mem_Ico] at hj; rw [mem_range]; omega
      · intro j hj hj'
        rw [mem_range] at hj; rw [mem_Ico] at hj'
        rw [hout j hj (by omega), sub_self]
    rw [← hsub, sum_Ico_eq_sum_range, show k + w - k = w by omega, hX, mul_sum]
    apply sum_congr rfl
    intro s hs
    have hs' := mem_range.mp hs
    have hma : m ≤ psum v (k + s) := by
      have := hdn (k + s) (by omega); have := hmono s; omega
    have hmc : m ≤ psum (NormGoal.chr r A) (k + s) := by have := hmono s; omega
    have e3 : (3 : ℤ) ^ (r - 1 - (k + s)) = 3 ^ (r - k - w) * 3 ^ (w - 1 - s) := by
      rw [← pow_add]; congr 1; omega
    have ea : (2 : ℤ) ^ psum v (k + s) = 2 ^ m * 2 ^ (psum v (k + s) - m) := by
      rw [← pow_add]; congr 1; omega
    have ec : (2 : ℤ) ^ psum (NormGoal.chr r A) (k + s) =
        2 ^ m * 2 ^ (psum (NormGoal.chr r A) (k + s) - m) := by
      rw [← pow_add]; congr 1; omega
    rw [e3, ea, ec]; ring
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero, sub_eq_zero] at hDX
    exact hBne (by exact_mod_cast hDX)
  have hSX : (S : ℤ) ∣ X := by
    rw [hDX] at hSD
    have c3 : IsCoprime (S : ℤ) 3 := by
      have := Nat.isCoprime_iff_coprime.mpr hS3.symm; simpa using this
    have c2 : IsCoprime (S : ℤ) 2 := by
      have := Nat.isCoprime_iff_coprime.mpr hS2.symm; simpa using this
    exact ((c3.pow_right (n := r - k - w)).mul_right (c2.pow_right (n := m))).dvd_of_dvd_mul_left hSD
  -- size
  clear_value X m
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · exfalso; apply hX0; rw [hX, h0]; simp
    · exact h0
  set N : ℕ → ℕ := fun s => 3 ^ (w - 1 - s) * 2 ^ (s * A / r) with hN
  have hterm : ∀ s ∈ range w, |(3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ (psum v (k + s) - m) - 2 ^ (psum (NormGoal.chr r A) (k + s) - m))| ≤
      2 ^ (2 * h + 1) * (N s : ℤ) := by
    intro s hs
    have hs' := mem_range.mp hs
    have hcs : psum (NormGoal.chr r A) (k + s) ≤ psum (NormGoal.chr r A) k + s * A / r + 1 := by
      rw [hc, hc, add_mul]; exact div_add_le _ _ _ hr0
    have hu := hup (k + s) (by omega)
    have hx1 : psum v (k + s) - m ≤ s * A / r + (2 * h + 1) ∧
        psum (NormGoal.chr r A) (k + s) - m ≤ s * A / r + (2 * h + 1) := by
      generalize s * A / r = Z at hcs ⊢
      omega
    have hb := abs_two_pow_sub_le (x := psum v (k + s) - m)
      (y := psum (NormGoal.chr r A) (k + s) - m) (z := s * A / r + (2 * h + 1)) hx1.1 hx1.2
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ (w - 1 - s))]
    calc (3 : ℤ) ^ (w - 1 - s) * |(2 : ℤ) ^ (psum v (k + s) - m) -
          2 ^ (psum (NormGoal.chr r A) (k + s) - m)|
        ≤ 3 ^ (w - 1 - s) * 2 ^ (s * A / r + (2 * h + 1)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 ^ (2 * h + 1) * (N s : ℤ) := by simp only [hN]; push_cast; rw [pow_add]; ring
  obtain ⟨s0, hs0, hmax⟩ := exists_max_image (range w) N (nonempty_range_iff.mpr (by omega))
  have hXle : |X| ≤ (w * 2 ^ (2 * h + 1) * N s0 : ℕ) := by
    calc |X| ≤ ∑ s ∈ range w, |(3 : ℤ) ^ (w - 1 - s) *
          ((2 : ℤ) ^ (psum v (k + s) - m) - 2 ^ (psum (NormGoal.chr r A) (k + s) - m))| :=
          by rw [hX]; exact abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range w, (2 ^ (2 * h + 1) * (N s0 : ℤ)) := by
          apply sum_le_sum; intro s hs
          refine (hterm s hs).trans ?_
          have := hmax s hs
          have : (N s : ℤ) ≤ N s0 := by exact_mod_cast this
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = (w * 2 ^ (2 * h + 1) * N s0 : ℕ) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  -- N s0 ^ r ≤ 2^{(w-1)A}
  have hNr : N s0 ^ r ≤ 2 ^ ((w - 1) * A) := by
    have hs0' := mem_range.mp hs0
    simp only [hN]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have h3 : 3 ^ ((w - 1 - s0) * r) ≤ 2 ^ ((w - 1 - s0) * A) := by
      rw [mul_comm (w - 1 - s0) r, mul_comm (w - 1 - s0) A, pow_mul, pow_mul]
      exact Nat.pow_le_pow_left (by omega) _
    have h2 : 2 ^ (s0 * A / r * r) ≤ 2 ^ (s0 * A) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self _ _)
    calc 3 ^ ((w - 1 - s0) * r) * 2 ^ (s0 * A / r * r)
        ≤ 2 ^ ((w - 1 - s0) * A) * 2 ^ (s0 * A) := Nat.mul_le_mul h3 h2
      _ = 2 ^ ((w - 1) * A) := by
          rw [← pow_add]; congr 1
          rw [← add_mul]; congr 1; omega
  have hlt : w * 2 ^ (2 * h + 1) * N s0 < 2 ^ (A - A / d) := by
    rw [← Nat.pow_lt_pow_iff_left (show r ≠ 0 by omega), mul_pow, ← pow_mul]
    calc (w * 2 ^ (2 * h + 1)) ^ r * N s0 ^ r ≤ (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * A) :=
          Nat.mul_le_mul_left _ hNr
      _ < 2 ^ ((A - A / d) * r) := hW
  have hAd : A / d = A' := by
    rw [hA']; exact Nat.mul_div_cancel_left _ (by omega)
  have hUS : 2 ^ (A - A / d) ≤ S := by
    obtain ⟨e, he⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    have := Sg_ge_two (2 ^ A') (3 ^ r') e
    have hA2 : A - A / d = A' * (e + 1) := by
      rw [hAd]
      have : A = A' * (e + 1) + A' := by rw [hA', he]; ring
      omega
    rw [hA2, pow_mul, hSdef, he]
    omega
  have hXS : |X| < S := by
    calc |X| ≤ (w * 2 ^ (2 * h + 1) * N s0 : ℕ) := hXle
      _ < (S : ℤ) := by exact_mod_cast (lt_of_lt_of_le hlt hUS)
  exact not_dvd_of_abs_lt hX0 hXS hSX

section Cycle
open CollatzProof

/-- **Cycle form of T3.** No positive `T`-cycle with `r ≥ 2` odd steps and period `L`,
`gcd(L, r) ≥ 2`, has a valuation word whose partial sums leave those of `chr r L` only inside
a window `[k, k + w)`, by at most `h`, when `(w 2^{2h+1})^r 2^{(w-1)L} < 2^{(L - L/d) r}`. -/
theorem cycle_window_noncoprime {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hd : 2 ≤ Nat.gcd L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k w h : ℕ) (hkw : k + w ≤ r)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * L) < 2 ^ ((L - L / Nat.gcd L r) * r))
    (hout : ∀ j < r, (j < k ∨ k + w ≤ j) → psum v j = psum (NormGoal.chr r L) j)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r L) j + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r L) j ≤ psum v j + h)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r L) j) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  exact no_cycle_window_noncoprime r L hd hq k w h hkw hW v (fun i hi => hv1 i (by omega))
    hout hup hdn hne hdiv

end Cycle
end Collatz.NormWindow

#print axioms Collatz.NormWindow.Bnum_inj
#print axioms Collatz.NormWindow.no_cycle_window_noncoprime
#print axioms Collatz.NormWindow.cycle_window_noncoprime
