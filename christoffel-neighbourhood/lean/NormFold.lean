import NormPlateau

/-!
# the self-fold modulo `Φ_p(2^{A/p}, 3^{r/p})`

Notation: `psum v j = P_j`, `B(v) = Σ_{j<r} 3^{r-1-j} 2^{P_j}` (Böhm–Sontacchi numerator),
`q = 2^A - 3^r`. For `p ∣ gcd(A, r)`, `r = p r'`, `A = p A'`, `U = 2^{A'}`, `V = 3^{r'}`,
`Φ = Σ_{t<p} U^t V^{p-1-t}` divides `q`, is coprime to `6`, and is `≥ U^{p-1}`. For `p = d` this
is Solomon's cofactor `S_d` (Solomon 2026, Zenodo 22220730, Prop. 6.3); for `p = 2`,
`Φ = 2^{A/2} + 3^{r/2}`.

New idea (`NormFold`): compare `B(v)` with **its own `r'`-shift** modulo `Φ`, instead of with
`B(chr)`. Modulo `Φ`, `U^{p-1} B(v)` folds into a sum over the non-pivot indices of
`3^{·}(2^{α_i} - 2^{β_i})`, where `β_i` is the partial sum at the pivot index of the same
column `i mod r'`, shifted by a multiple of `A'`; the term vanishes when `v` is `r'`-periodic at
that column. So only *bad columns* `{j < r' : P(j + t r') ≠ P j + t A' for some t}` matter, and
they need only lie in an arc of `ℤ/r'` of length `r' - g` (not an arc of `ℤ/r`), which the
free-gap lemma provides as soon as `|bad columns| · g < r'`.

* `window_pair`: the `NormArc` size core (`NormArc.window_core`) for two free increasing sequences.
* `fold_two`: the exact fold identity for `p = 2`.
* **T1** `no_cycle_half_fold` (`p = 2`): bad columns in one cyclic arc of `ℤ/r'`.
* **T3** `no_cycle_half_fold_count`: fewer than `r'/g` bad columns, anywhere;
  `no_cycle_sites_even`: a word within `e` of `chr r A` (`r, A` even), not `r'`-periodic,
  deviating from chr at fewer than `r'/g` indices (arbitrary positions); cycle forms
  `cycle_half_fold_count`, `cycle_sites_even`; non-vacuity `witness_fold` (`r = 40902`,
  `L = 64830`, `e = 1`, `g = 14`: up to 1460 deviating indices), `witness_fold2` (`L = 64832`,
  `gcd = 2`).
* **T2** (any common factor `p = n + 1 ≥ 2` of `r` and `A`): `fold_top` (top-pivot fold
  identity, pure algebra), `rot_fold` (rotation modulo `q`), `fold_core` (window theorem in
  rotated coordinates; needs the start column good), `no_cycle_fold_count` (between `1` and
  fewer than `r'/g` bad columns, anywhere, `(n r' 2^{2h+1})^2 < 2^{3(g+1)}`),
  `no_cycle_sites_fold` (any `p`: few deviating sites from chr, any positions), cycle forms
  `cycle_fold_count`, `cycle_sites_fold`, witnesses `witness_fold3` (`r = 122703`,
  `L = 194484`, `p = 3`: `|D| ≤ 2726`) and `witness_fold4` (`r = 122704`, `p = 4`: `|D| ≤ 2045`).
  Compare `NormArc` (`NormArc`): at most `d - 1` sites.

Scope: word-level statements (and their `T`-cycle forms) for `r` and `A` with a common
factor `p ≥ 2` (T1/T3: both even);
height of the deviation bounded; `r'`-periodic words are not excluded (they reduce to `(r', A')`,
possibly coprime). It does not touch coprime `(r, A)` (the generic case) or the
`d = 2` middle band of `NormPlateau` slides (there every column is bad). Prior art: Solomon (cofactor
`S_d`), Knight, Lebel, Mghirbi, Fernández–Ibáñez (arXiv 2607.24844); novelty of the self-fold
is provisional.
-/

namespace Collatz.NormFold
open Collatz.NormGoal Collatz.NormReduce Collatz.NormAll
  Collatz.NormCofactor Collatz.NormWindow Collatz.NormArc Finset

theorem window_pair {r A E H w m S : ℕ} (hr0 : 0 < r) (h3r : 3 ^ r ≤ 2 ^ A)
    (hS2 : Nat.Coprime 2 S) (hUS : 2 ^ E ≤ S)
    (hW : (w * 2 ^ H) ^ r * 2 ^ ((w - 1) * A) < 2 ^ (E * r))
    (f g : ℕ → ℕ) (hf : ∀ s, s + 1 < w → f s < f (s + 1))
    (hg : ∀ s, s + 1 < w → g s < g (s + 1))
    (hfl : ∀ s < w, m ≤ f s) (hgl : ∀ s < w, m ≤ g s)
    (hfu : ∀ s < w, f s ≤ m + s * A / r + H) (hgu : ∀ s < w, g s ≤ m + s * A / r + H)
    (hne : ∃ s < w, f s ≠ g s)
    (hdvd : (S : ℤ) ∣ ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) * ((2 : ℤ) ^ f s - 2 ^ g s)) :
    False := by
  set X : ℤ := ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
    ((2 : ℤ) ^ (f s - m) - 2 ^ (g s - m)) with hX
  have hTX : ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) * ((2 : ℤ) ^ f s - 2 ^ g s) = 2 ^ m * X := by
    rw [hX, mul_sum]
    apply sum_congr rfl
    intro s hs
    have hs' := mem_range.mp hs
    have ea : (2 : ℤ) ^ f s = 2 ^ m * 2 ^ (f s - m) := by
      rw [← pow_add]; congr 1; have := hfl s hs'; omega
    have ec : (2 : ℤ) ^ g s = 2 ^ m * 2 ^ (g s - m) := by
      rw [← pow_add]; congr 1; have := hgl s hs'; omega
    rw [ea, ec]; ring
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hTX
    simp only [mul_sub, sum_sub_distrib, sub_eq_zero] at hTX
    have hN : ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ f s =
        ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ g s := by exact_mod_cast hTX
    obtain ⟨s0, hs0, hne0⟩ := hne
    exact hne0 (seq_inj hf hg hN s0 hs0)
  have hSX : (S : ℤ) ∣ X := by
    rw [hTX] at hdvd
    have c2 : IsCoprime (S : ℤ) 2 := by
      have := Nat.isCoprime_iff_coprime.mpr hS2.symm; simpa using this
    exact (c2.pow_right (n := m)).dvd_of_dvd_mul_left hdvd
  clear_value X
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · exfalso; apply hX0; rw [hX, h0]; simp
    · exact h0
  set N : ℕ → ℕ := fun s => 3 ^ (w - 1 - s) * 2 ^ (s * A / r) with hN
  have hterm : ∀ s ∈ range w, |(3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ (f s - m) - 2 ^ (g s - m))| ≤ 2 ^ H * (N s : ℤ) := by
    intro s hs
    have hs' := mem_range.mp hs
    have h1 := hfu s hs'
    have h2 := hgu s hs'
    have hx1 : f s - m ≤ s * A / r + H ∧ g s - m ≤ s * A / r + H := by
      generalize s * A / r = Z at h1 h2 ⊢
      omega
    have hb := abs_two_pow_sub_le (x := f s - m) (y := g s - m) (z := s * A / r + H)
      hx1.1 hx1.2
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ (w - 1 - s))]
    calc (3 : ℤ) ^ (w - 1 - s) * |(2 : ℤ) ^ (f s - m) - 2 ^ (g s - m)|
        ≤ 3 ^ (w - 1 - s) * 2 ^ (s * A / r + H) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 ^ H * (N s : ℤ) := by simp only [hN]; push_cast; rw [pow_add]; ring
  obtain ⟨s0, hs0, hmax⟩ := exists_max_image (range w) N (nonempty_range_iff.mpr (by omega))
  have hXle : |X| ≤ (w * 2 ^ H * N s0 : ℕ) := by
    calc |X| ≤ ∑ s ∈ range w, |(3 : ℤ) ^ (w - 1 - s) *
          ((2 : ℤ) ^ (f s - m) - 2 ^ (g s - m))| := by rw [hX]; exact abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range w, (2 ^ H * (N s0 : ℤ)) := by
          apply sum_le_sum; intro s hs
          refine (hterm s hs).trans ?_
          have := hmax s hs
          have : (N s : ℤ) ≤ N s0 := by exact_mod_cast this
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = (w * 2 ^ H * N s0 : ℕ) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hNr : N s0 ^ r ≤ 2 ^ ((w - 1) * A) := by
    have hs0' := mem_range.mp hs0
    simp only [hN]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have h3 : 3 ^ ((w - 1 - s0) * r) ≤ 2 ^ ((w - 1 - s0) * A) := by
      rw [mul_comm (w - 1 - s0) r, mul_comm (w - 1 - s0) A, pow_mul, pow_mul]
      exact Nat.pow_le_pow_left h3r _
    have h2 : 2 ^ (s0 * A / r * r) ≤ 2 ^ (s0 * A) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self _ _)
    calc 3 ^ ((w - 1 - s0) * r) * 2 ^ (s0 * A / r * r)
        ≤ 2 ^ ((w - 1 - s0) * A) * 2 ^ (s0 * A) := Nat.mul_le_mul h3 h2
      _ = 2 ^ ((w - 1) * A) := by
          rw [← pow_add]; congr 1
          rw [← add_mul]; congr 1; omega
  have hlt : w * 2 ^ H * N s0 < 2 ^ E := by
    rw [← Nat.pow_lt_pow_iff_left (show r ≠ 0 by omega), mul_pow, ← pow_mul]
    calc (w * 2 ^ H) ^ r * N s0 ^ r ≤ (w * 2 ^ H) ^ r * 2 ^ ((w - 1) * A) :=
          Nat.mul_le_mul_left _ hNr
      _ < 2 ^ (E * r) := hW
  have hXS : |X| < S := by
    calc |X| ≤ (w * 2 ^ H * N s0 : ℕ) := hXle
      _ < (S : ℤ) := by exact_mod_cast (lt_of_lt_of_le hlt hUS)
  exact not_dvd_of_abs_lt hX0 hXS hSX

/-- `r x ≤ y + r h ⇒ x ≤ ⌊y/r⌋ + h`. -/
theorem floor_up {r x y h : ℕ} (hr : 0 < r) (H : r * x ≤ y + r * h) : x ≤ y / r + h := by
  have : (x - h) * r ≤ y := by
    rw [Nat.sub_mul]; have := Nat.mul_comm r x; have := Nat.mul_comm r h; omega
  have := (Nat.le_div_iff_mul_le hr).mpr this
  omega

theorem psum_add_le {v : ℕ → ℕ} {n : ℕ} (hv1 : ∀ i < n, 1 ≤ v i) (i : ℕ) :
    ∀ d, i + d ≤ n → psum v i + d ≤ psum v (i + d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have := ih (by omega)
    rw [show i + (d + 1) = (i + d) + 1 by ring, psum_succ]
    have := hv1 (i + d) (by omega)
    omega

theorem psum_lt {v : ℕ → ℕ} {n i j : ℕ} (hv1 : ∀ i < n, 1 ≤ v i) (hij : i < j) (hj : j ≤ n) :
    psum v i < psum v j := by
  have := psum_add_le hv1 i (j - i) (by omega)
  rw [show i + (j - i) = j by omega] at this
  omega

theorem psum_le {v : ℕ → ℕ} {n i j : ℕ} (hv1 : ∀ i < n, 1 ≤ v i) (hij : i ≤ j) (hj : j ≤ n) :
    psum v i ≤ psum v j := by
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · exact (psum_lt hv1 h hj).le

/-- Fold sum exponents for `p = 2`. -/
def fα (A' k : ℕ) (v : ℕ → ℕ) (s : ℕ) : ℕ := psum v (k + s) + A'

def fβ (r' A' k : ℕ) (v : ℕ → ℕ) (s : ℕ) : ℕ :=
  if k + s < r' then psum v (k + s + r') else psum v (k + s - r') + 2 * A'

/-- **Fold identity (p = 2).** With `U = 2^{A'}`, `Φ = 2^{A'} + 3^{r'}`, `k < r'`:
`Φ ∣ U·B(v) - 3^{r'-k} Σ_{s<r'} 3^{r'-1-s}(2^{α_{k+s}} - 2^{β_{k+s}})`. -/
theorem fold_two (r' A' k : ℕ) (hk : k < r') (v : ℕ → ℕ) :
    ((2 : ℤ) ^ A' + 3 ^ r') ∣ (2 : ℤ) ^ A' * (Bnum (2 * r') v : ℤ) -
      3 ^ (r' - k) * ∑ s ∈ range r', (3 : ℤ) ^ (r' - 1 - s) *
        ((2 : ℤ) ^ fα A' k v s - 2 ^ fβ r' A' k v s) := by
  set P := psum v with hP
  set U : ℤ := 2 ^ A' with hU
  set V : ℤ := 3 ^ r' with hV
  set colB : ℕ → ℤ := fun j => (3 : ℤ) ^ (2 * r' - 1 - j) * 2 ^ P j +
    3 ^ (r' - 1 - j) * 2 ^ P (j + r') with hcol
  set Ft : ℕ → ℤ := fun s => (3 : ℤ) ^ (r' - 1 - s) *
        ((2 : ℤ) ^ fα A' k v s - 2 ^ fβ r' A' k v s) with hFt
  have hB : (Bnum (2 * r') v : ℤ) = ∑ j ∈ range r', colB j := by
    rw [cast_Bnum, show 2 * r' = r' + r' by ring, sum_range_add, ← sum_add_distrib]
    apply sum_congr rfl; intro j hj
    simp only [hcol, hP]
    rw [show r' + r' - 1 - (r' + j) = r' - 1 - j by omega, add_comm r' j, two_mul]
  have hB2 : ∑ j ∈ range r', colB j = ∑ t ∈ range k, colB t +
      ∑ s ∈ range (r' - k), colB (k + s) := by
    rw [← sum_range_add, show k + (r' - k) = r' by omega]
  have hF2 : ∑ s ∈ range r', Ft s = ∑ s ∈ range (r' - k), Ft s +
      ∑ t ∈ range k, Ft (r' - k + t) := by
    rw [← sum_range_add, show r' - k + k = r' by omega]
  change (U + V) ∣ U * (Bnum (2 * r') v : ℤ) - 3 ^ (r' - k) * ∑ s ∈ range r', Ft s
  rw [hB, hB2, hF2, mul_add, mul_add, mul_sum, mul_sum, mul_sum, mul_sum]
  have e : ∀ a b c d : ℤ, a + b - (c + d) = (a - d) + (b - c) := by intros; ring
  rw [e, ← sum_sub_distrib, ← sum_sub_distrib]
  apply dvd_add
  · apply dvd_sum; intro t ht
    have ht' := mem_range.mp ht
    refine ⟨3 ^ (r' - 1 - t) * 2 ^ P t * U, ?_⟩
    simp only [hcol, hFt, fα, fβ]
    rw [if_neg (by omega), show k + (r' - k + t) = t + r' by omega,
      show t + r' - r' = t by omega]
    have e1 : (3 : ℤ) ^ (2 * r' - 1 - t) = V * 3 ^ (r' - 1 - t) := by
      rw [hV, ← pow_add]; congr 1; omega
    have e2 : (3 : ℤ) ^ (r' - k) * 3 ^ (r' - 1 - (r' - k + t)) = 3 ^ (r' - 1 - t) := by
      rw [← pow_add]; congr 1; omega
    rw [e1, ← hP, pow_add, pow_add, show 2 * A' = A' + A' by ring, pow_add, ← hU]
    linear_combination (-(2:ℤ) ^ P (t + r') * U + 2 ^ P t * U * U) * e2
  · apply dvd_sum; intro s hs
    have hs' := mem_range.mp hs
    refine ⟨3 ^ (r' - 1 - (k + s)) * 2 ^ P (k + s + r'), ?_⟩
    simp only [hcol, hFt, fα, fβ]
    rw [if_pos (by omega)]
    have e1 : (3 : ℤ) ^ (2 * r' - 1 - (k + s)) = V * 3 ^ (r' - 1 - (k + s)) := by
      rw [hV, ← pow_add]; congr 1; omega
    have e2 : (3 : ℤ) ^ (r' - k) * 3 ^ (r' - 1 - s) = V * 3 ^ (r' - 1 - (k + s)) := by
      rw [hV, ← pow_add, ← pow_add]; congr 1; omega
    rw [e1, ← hP, pow_add, ← hU]
    linear_combination (-(2:ℤ) ^ P (k + s) * U + 2 ^ P (k + s + r')) * e2


theorem three_lt_of_hq {r' A' : ℕ} (hq : 3 ^ (2 * r') + 1 < 2 ^ (2 * A')) : 3 ^ r' < 2 ^ A' := by
  by_contra h
  push Not at h
  have : 2 ^ (2 * A') ≤ 3 ^ (2 * r') := by
    rw [pow_mul', pow_mul']; exact Nat.pow_le_pow_left h 2
  omega

theorem coprime_two_Phi {r' A' : ℕ} (hA : 0 < A') : Nat.Coprime 2 (2 ^ A' + 3 ^ r') := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h
  have h2 : 2 ∣ 3 ^ r' := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

theorem coprime_three_Phi {r' A' : ℕ} (hr : 0 < r') : Nat.Coprime 3 (2 ^ A' + 3 ^ r') := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h
  have h2 : 3 ∣ 2 ^ A' := (Nat.dvd_add_left (dvd_pow_self 3 (by omega))).mp h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

/-- **T1: the self-fold for `p = 2`.** Let `r = 2r'`, `A = 2A'`, `3^r + 1 < 2^A`,
`v` with entries `≥ 1` below `r`, `psum v r = A`, two-sided `h`-balanced
(`|P_j - P_i - (j-i)A/r| ≤ h`, stated with `r', A'`), `h ≤ A'`. Call column `j < r'` *good* if
`P(j + r') = P j + A'` (`v` is `r'`-periodic there). If the bad columns are nonempty and lie in
the cyclic arc `[k, k+w)` of `ℤ/r'`, and `(w 2^{2h+1})^{r'} 2^{(w-1)A'} < 2^{A' r'}`, then
`(2^A - 3^r) ∤ B(v)`. Proof: modulo `Φ = 2^{A'} + 3^{r'}` (which divides `2^A - 3^r`; for
`d = 2` this is Solomon's `S_2`), `2^{A'} B(v)` folds into a sum over one period of
`3^{·}(2^{α_i} - 2^{β_i})`, `β_i` the partial sum at the partner index `i ± r'`, shifted
(`fold_two`); good columns drop out, leaving a window over the arc, and `window_pair`
(2-adic injectivity + size) finishes. -/
theorem no_cycle_half_fold (r' A' h k w : ℕ) (hr' : 0 < r')
    (hq : 3 ^ (2 * r') + 1 < 2 ^ (2 * A')) (hhA : h ≤ A')
    (v : ℕ → ℕ) (hv1 : ∀ i < 2 * r', 1 ≤ v i) (hsum : psum v (2 * r') = 2 * A')
    (hbal : ∀ i j, i ≤ j → j ≤ 2 * r' →
        (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * h ∧
        r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * h)
    (hk : k < r') (hw : w ≤ r')
    (hW : (w * 2 ^ (2 * h + 1)) ^ r' * 2 ^ ((w - 1) * A') < 2 ^ (A' * r'))
    (hout : ∀ j < r', ¬ inArc r' k w j → psum v (j + r') = psum v j + A')
    (hne : ∃ j < r', psum v (j + r') ≠ psum v j + A') :
    ¬ (2 ^ (2 * A') - 3 ^ (2 * r')) ∣ Bnum (2 * r') v := by
  intro hdiv
  have h3 := three_lt_of_hq hq
  have hA0 : 0 < A' := by
    rcases Nat.eq_zero_or_pos A' with h0 | h0
    · rw [h0] at h3; have := Nat.one_le_pow r' 3 (by norm_num); simp at h3
    · exact h0
  set Φ := 2 ^ A' + 3 ^ r' with hΦ
  have hΦ2 := coprime_two_Phi (r' := r') hA0
  have hΦ3 : IsCoprime (Φ : ℤ) (3 : ℤ) := by
    have := Nat.isCoprime_iff_coprime.mpr (coprime_three_Phi (A' := A') hr').symm
    simpa [hΦ] using this
  have hΦB : (Φ : ℤ) ∣ (Bnum (2 * r') v : ℤ) := by
    have hq' := Int.natCast_dvd_natCast.mpr hdiv
    rw [Nat.cast_sub (by omega)] at hq'
    refine dvd_trans ⟨(2 : ℤ) ^ A' - 3 ^ r', ?_⟩ hq'
    rw [hΦ]; push_cast; rw [pow_mul', pow_mul']; ring
  have hfold := fold_two r' A' k hk v
  set Ft : ℕ → ℤ := fun s => (3 : ℤ) ^ (r' - 1 - s) *
        ((2 : ℤ) ^ fα A' k v s - 2 ^ fβ r' A' k v s) with hFt
  have hΦF : (Φ : ℤ) ∣ ∑ s ∈ range r', Ft s := by
    have h1 : (Φ : ℤ) ∣ 3 ^ (r' - k) * ∑ s ∈ range r', Ft s := by
      have h2 : (Φ : ℤ) ∣ (2 : ℤ) ^ A' * (Bnum (2 * r') v : ℤ) := dvd_mul_of_dvd_right hΦB _
      have h3 : ((Φ : ℕ) : ℤ) = (2 : ℤ) ^ A' + 3 ^ r' := by rw [hΦ]; push_cast; ring
      rw [← h3] at hfold
      have := dvd_sub h2 hfold
      simpa using this
    exact (hΦ3.pow_right).dvd_of_dvd_mul_left h1
  -- good columns vanish
  have hgood : ∀ s, w ≤ s → s < r' → fα A' k v s = fβ r' A' k v s := by
    intro s hws hsr
    unfold fα fβ
    split_ifs with hc
    · have := hout (k + s) hc (by unfold inArc; omega); omega
    · have := hout (k + s - r') (by omega) (by unfold inArc; omega)
      rw [show k + s - r' + r' = k + s by omega] at this; omega
  have hX : (Φ : ℤ) ∣ ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ fα A' k v s - 2 ^ fβ r' A' k v s) := by
    have hsplit : ∑ s ∈ range r', Ft s = ∑ s ∈ range w, Ft s + ∑ s ∈ range (r' - w), Ft (w + s) := by
      rw [← sum_range_add, show w + (r' - w) = r' by omega]
    have hz : ∑ s ∈ range (r' - w), Ft (w + s) = 0 := by
      apply sum_eq_zero; intro s hs
      have := mem_range.mp hs
      simp only [hFt]; rw [hgood (w + s) (by omega) (by omega), sub_self, mul_zero]
    have hw3 : ∑ s ∈ range w, Ft s = 3 ^ (r' - w) * ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
        ((2 : ℤ) ^ fα A' k v s - 2 ^ fβ r' A' k v s) := by
      rw [mul_sum]; apply sum_congr rfl; intro s hs
      have := mem_range.mp hs
      simp only [hFt]; rw [← mul_assoc, ← pow_add]; congr 2; omega
    rw [hsplit, hz, add_zero, hw3] at hΦF
    exact (hΦ3.pow_right).dvd_of_dvd_mul_left hΦF
  -- bounds
  set m := psum v k + A' - h with hm
  have hPk : ∀ s, s < r' → psum v k ≤ psum v (k + s) := fun s hs => psum_le hv1 (by omega) (by omega)
  refine window_pair (r := r') (A := A') (E := A') (H := 2 * h + 1) (w := w) (m := m) (S := Φ)
    hr' h3.le hΦ2 (by rw [hΦ]; exact Nat.le_add_right _ _) (by rw [mul_comm A' r'] at hW ⊢; exact hW)
    (fα A' k v) (fβ r' A' k v) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hX
  · intro s hs; unfold fα
    have := psum_lt (v := v) hv1 (i := k + s) (j := k + (s + 1)) (by omega) (by omega); omega
  · intro s hs; unfold fβ
    by_cases h1 : k + s + 1 < r'
    · rw [if_pos (by omega), if_pos (by omega)]
      exact psum_lt hv1 (by omega) (by omega)
    · by_cases h2 : k + s < r'
      · rw [if_pos h2, if_neg (by omega), show k + (s + 1) - r' = 0 by omega]
        have := psum_lt (v := v) hv1 (i := k + s + r') (j := 2 * r') (by omega) le_rfl
        have p0 : psum v 0 = 0 := by simp [psum]
        rw [hsum] at this; rw [p0]; omega
      · rw [if_neg h2, if_neg (by omega)]
        have := psum_lt (v := v) hv1 (i := k + s - r') (j := k + (s + 1) - r') (by omega) (by omega)
        omega
  · intro s hs; unfold fα; have := hPk s (by omega); omega
  · intro s hs; unfold fβ
    split_ifs with hc
    · have hb := (hbal k (k + s + r') (by omega) (by omega)).1
      rw [show k + s + r' - k = s + r' by omega] at hb
      have hle := psum_le (v := v) hv1 (i := k) (j := k + s + r') (by omega) (by omega)
      set D := psum v (k + s + r') - psum v k
      have e1 := add_mul s r' A'
      have e2 := mul_add r' D h
      have : r' * A' ≤ r' * (D + h) := by
        have := Nat.zero_le (s * A'); omega
      have := Nat.le_of_mul_le_mul_left this hr'
      omega
    · have hb := (hbal (k + s - r') k (by omega) (by omega)).2
      rw [show k - (k + s - r') = r' - s by omega] at hb
      have hle := psum_le (v := v) hv1 (i := k + s - r') (j := k) (by omega) (by omega)
      set D := psum v k - psum v (k + s - r')
      have e1 : (r' - s) * A' ≤ r' * A' := Nat.mul_le_mul_right _ (by omega)
      have e2 := mul_add r' A' h
      have : r' * D ≤ r' * (A' + h) := by omega
      have := Nat.le_of_mul_le_mul_left this hr'
      omega
  · intro s hs; unfold fα
    have hb := (hbal k (k + s) (by omega) (by omega)).2
    rw [show k + s - k = s by omega] at hb
    have hle := hPk s (by omega)
    have := floor_up hr' hb
    omega
  · intro s hs; unfold fβ
    split_ifs with hc
    · have hb := (hbal k (k + s + r') (by omega) (by omega)).2
      rw [show k + s + r' - k = s + r' by omega] at hb
      have hle := psum_le (v := v) hv1 (i := k) (j := k + s + r') (by omega) (by omega)
      set D := psum v (k + s + r') - psum v k
      have e1 := add_mul s r' A'
      have e2 := mul_add r' A' h
      have := floor_up (x := D) (y := s * A') (h := A' + h) hr' (by omega)
      omega
    · have hb := (hbal (k + s - r') k (by omega) (by omega)).1
      rw [show k - (k + s - r') = r' - s by omega] at hb
      have hle := psum_le (v := v) hv1 (i := k + s - r') (j := k) (by omega) (by omega)
      set D := psum v k - psum v (k + s - r')
      have e1 : (r' - s) * A' + s * A' = r' * A' := by
        rw [← add_mul, Nat.sub_add_cancel (by omega)]
      have e2 := mul_add r' D h
      have := floor_up (x := A') (y := s * A') (h := D + h) hr' (by omega)
      omega
  · obtain ⟨j0, hj0, hne0⟩ := hne
    have hin : inArc r' k w j0 := by
      by_contra hc; exact hne0 (hout j0 hj0 hc)
    rcases hin with ⟨h1, h2⟩ | h1
    · refine ⟨j0 - k, by omega, ?_⟩
      unfold fα fβ; rw [if_pos (by omega), show k + (j0 - k) = j0 by omega]; omega
    · refine ⟨j0 + r' - k, by omega, ?_⟩
      unfold fα fβ; rw [if_neg (by omega), show k + (j0 + r' - k) = j0 + r' by omega,
        show j0 + r' - r' = j0 by omega]; omega


/-- **Cheap sufficient condition for the arc hypothesis.** If `3r' ≤ 2A'`, `w + g ≤ r'` and
`(r' 2^{2h+1})^2 < 2^{3(g+1)}`, then `(w 2^{2h+1})^{r'} 2^{(w-1)A'} < 2^{A' r'}`. -/
theorem hW_fold {r' A' h g w : ℕ} (hr' : 0 < r') (h3 : 3 * r' ≤ 2 * A') (hwg : w + g ≤ r')
    (hx : (r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1))) :
    (w * 2 ^ (2 * h + 1)) ^ r' * 2 ^ ((w - 1) * A') < 2 ^ (A' * r') := by
  rcases Nat.eq_zero_or_pos w with hw0 | hw0
  · rw [hw0, zero_mul, zero_pow (by omega), zero_mul]; positivity
  set x := r' * 2 ^ (2 * h + 1) with hxdef
  have hxr : x ^ r' < 2 ^ ((g + 1) * A') := by
    have h2 : (x ^ r') ^ 2 < (2 ^ ((g + 1) * A')) ^ 2 := by
      calc (x ^ r') ^ 2 = (x ^ 2) ^ r' := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ < (2 ^ (3 * (g + 1))) ^ r' := Nat.pow_lt_pow_left hx (by omega)
        _ = 2 ^ ((g + 1) * (3 * r')) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ ((g + 1) * (2 * A')) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h3)
        _ = (2 ^ ((g + 1) * A')) ^ 2 := by rw [← pow_mul]; ring_nf
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
  have hle : (w * 2 ^ (2 * h + 1)) ^ r' ≤ x ^ r' :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega)) _
  calc (w * 2 ^ (2 * h + 1)) ^ r' * 2 ^ ((w - 1) * A') ≤ x ^ r' * 2 ^ ((w - 1) * A') :=
        Nat.mul_le_mul_right _ hle
    _ < 2 ^ ((g + 1) * A') * 2 ^ ((w - 1) * A') :=
        Nat.mul_lt_mul_of_pos_right hxr (by positivity)
    _ = 2 ^ ((w + g) * A') := by
        rw [← pow_add, ← add_mul]; congr 2; omega
    _ ≤ 2 ^ (A' * r') := by
        rw [mul_comm A' r']; exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hwg)

theorem three_le_of_hq {r' A' : ℕ} (hq : 3 ^ (2 * r') + 1 < 2 ^ (2 * A')) : 3 * r' ≤ 2 * A' := by
  have h1 : 2 ^ (3 * r') ≤ 3 ^ (2 * r') := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
  have : 2 ^ (3 * r') < 2 ^ (2 * A') := by omega
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).mp this).le

/-- The bad columns of `v` for `p = 2`: `j < r'` with `P(j + r') ≠ P j + A'`. -/
def badCols (r' A' : ℕ) (v : ℕ → ℕ) : Finset ℕ :=
  (range r').filter (fun j => psum v (j + r') ≠ psum v j + A')

/-- **T3c: few bad columns, anywhere.** Same setting as `no_cycle_half_fold`; if the
set `C` of bad columns satisfies `1 ≤ |C|` and `|C|·g < r'`, with
`(r' 2^{2h+1})^2 < 2^{3(g+1)}`, then `(2^A - 3^r) ∤ B(v)`. No condition on where the bad columns
are: a free gap of `g` good columns (double counting, `free_gap`) supplies the arc. -/
theorem no_cycle_half_fold_count (r' A' h g : ℕ) (hr' : 0 < r')
    (hq : 3 ^ (2 * r') + 1 < 2 ^ (2 * A')) (hhA : h ≤ A')
    (v : ℕ → ℕ) (hv1 : ∀ i < 2 * r', 1 ≤ v i) (hsum : psum v (2 * r') = 2 * A')
    (hbal : ∀ i j, i ≤ j → j ≤ 2 * r' →
        (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * h ∧
        r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * h)
    (hx : (r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (hC0 : 0 < (badCols r' A' v).card) (hCg : (badCols r' A' v).card * g < r') :
    ¬ (2 ^ (2 * A') - 3 ^ (2 * r')) ∣ Bnum (2 * r') v := by
  set C := badCols r' A' v with hC
  have hCr : ∀ j ∈ C, j < r' := fun j hj => mem_range.mp (mem_filter.mp hj).1
  have hgr : g < r' := by
    have : 1 * g ≤ C.card * g := Nat.mul_le_mul_right _ hC0
    omega
  obtain ⟨x, hx', hfree⟩ := free_gap r' g C hCr hCg
  set k := if x + g < r' then x + g else x + g - r' with hk
  have hkr : k < r' := by rw [hk]; split_ifs <;> omega
  obtain ⟨j0, hj0⟩ := card_pos.mp hC0
  have hj0' := mem_filter.mp hj0
  refine no_cycle_half_fold r' A' h k (r' - g) hr' hq hhA v hv1 hsum hbal hkr (by omega)
    (hW_fold hr' (three_le_of_hq hq) (by omega) hx) ?_
    ⟨j0, mem_range.mp hj0'.1, hj0'.2⟩
  intro j hj hj'
  by_contra hne'
  have hjC : j ∈ C := mem_filter.mpr ⟨mem_range.mpr hj, hne'⟩
  have h2 := hfree j hjC
  unfold inArc at h2 hj'
  rw [hk] at hj'
  split_ifs at hj' with hc <;> omega

/-- **Closeness to chr gives balance.** If `|psum v j - ⌊jA'/r'⌋| ≤ e` for all `j ≤ 2r'` and the
entries are `≥ 1`, then `v` is two-sided `(2e+1)`-balanced (in the form used by
`no_cycle_half_fold`). -/
theorem bal_of_chr {r' A' e : ℕ} (hr' : 0 < r') (v : ℕ → ℕ) (hv1 : ∀ i < 2 * r', 1 ≤ v i)
    (hup : ∀ j ≤ 2 * r', psum v j ≤ j * A' / r' + e)
    (hdn : ∀ j ≤ 2 * r', j * A' / r' ≤ psum v j + e) :
    ∀ i j, i ≤ j → j ≤ 2 * r' →
        (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * (2 * e + 1) ∧
        r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * (2 * e + 1) := by
  intro i j hij hj
  have hle := psum_le hv1 hij hj
  have ui := hup i (by omega); have uj := hup j hj
  have di := hdn i (by omega); have dj := hdn j hj
  set Pi := psum v i; set Pj := psum v j
  set ci := i * A' / r'; set cj := j * A' / r'
  have hci1 : ci * r' ≤ i * A' := Nat.div_mul_le_self _ _
  have hcj1 : cj * r' ≤ j * A' := Nat.div_mul_le_self _ _
  have hci2 : i * A' < ci * r' + r' := Nat.lt_div_mul_add hr'
  have hcj2 : j * A' < cj * r' + r' := Nat.lt_div_mul_add hr'
  have m1 : r' * Pj ≤ r' * cj + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ uj
  have m2 : r' * cj ≤ r' * Pj + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ dj
  have m3 : r' * Pi ≤ r' * ci + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ ui
  have m4 : r' * ci ≤ r' * Pi + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ di
  have hia : i * A' ≤ j * A' := Nat.mul_le_mul_right _ hij
  have hPP : r' * Pi ≤ r' * Pj := Nat.mul_le_mul_left _ hle
  have e1 : r' * (2 * e + 1) = 2 * (r' * e) + r' := by ring
  rw [mul_comm ci r'] at hci1 hci2
  rw [mul_comm cj r'] at hcj1 hcj2
  rw [Nat.sub_mul, Nat.mul_sub, e1]
  constructor <;> omega

theorem chr_periodic {r' A' : ℕ} (hr' : 0 < r') (j : ℕ) :
    (j + r') * A' / r' = j * A' / r' + A' := by
  rw [add_mul, Nat.add_mul_div_left _ _ hr']

/-- **T3e: any few deviating sites from chr, at any positions (`r, A` even).** Let
`r = 2r'`, `A = 2A'`, `3^r + 1 < 2^A`, `2e + 1 ≤ A'`, and
`(r' 2^{2(2e+1)+1})^2 < 2^{3(g+1)}`. Let `v` have entries `≥ 1`, `psum v r = A`, partial sums
within `e` of those of `chr r A`, and equal to them outside a set `D` of indices with
`|D|·g < r'`. If `v` is not `r'`-periodic (`hne`), then `(2^A - 3^r) ∤ B(v)`. The positions of
the deviating indices are arbitrary. -/
theorem no_cycle_sites_even (r' A' e g : ℕ) (hr' : 0 < r')
    (hq : 3 ^ (2 * r') + 1 < 2 ^ (2 * A')) (he : 2 * e + 1 ≤ A')
    (hx : (r' * 2 ^ (2 * (2 * e + 1) + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (v : ℕ → ℕ) (hv1 : ∀ i < 2 * r', 1 ≤ v i) (hsum : psum v (2 * r') = 2 * A')
    (D : Finset ℕ) (hDg : D.card * g < r')
    (hout : ∀ j < 2 * r', j ∉ D → psum v j = psum (NormGoal.chr (2 * r') (2 * A')) j)
    (hup : ∀ j < 2 * r', psum v j ≤ psum (NormGoal.chr (2 * r') (2 * A')) j + e)
    (hdn : ∀ j < 2 * r', psum (NormGoal.chr (2 * r') (2 * A')) j ≤ psum v j + e)
    (hne : ∃ j < r', psum v (j + r') ≠ psum v j + A') :
    ¬ (2 ^ (2 * A') - 3 ^ (2 * r')) ∣ Bnum (2 * r') v := by
  have hc : ∀ j, psum (NormGoal.chr (2 * r') (2 * A')) j = j * A' / r' := fun j => psum_chr_two j
  have h2r : 2 * r' * A' / r' = 2 * A' := by
    rw [mul_comm 2 r', mul_assoc, Nat.mul_div_cancel_left _ hr']
  have hup' : ∀ j ≤ 2 * r', psum v j ≤ j * A' / r' + e := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · rw [← hc]; exact hup j h
    · rw [h, hsum, h2r]; omega
  have hdn' : ∀ j ≤ 2 * r', j * A' / r' ≤ psum v j + e := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · rw [← hc]; exact hdn j h
    · rw [h, hsum, h2r]; omega
  have hbal := bal_of_chr hr' v hv1 hup' hdn'
  have hCD : badCols r' A' v ⊆ D.image (fun i => i % r') := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_filter.mp hj
    have hj1 := mem_range.mp hj1
    rw [mem_image]
    by_cases hjD : j ∈ D
    · exact ⟨j, hjD, Nat.mod_eq_of_lt hj1⟩
    by_cases hjD' : j + r' ∈ D
    · exact ⟨j + r', hjD', by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj1]⟩
    exfalso; apply hj2
    rw [hout j (by omega) hjD, hout (j + r') (by omega) hjD', hc, hc, chr_periodic hr']
  have hcard : (badCols r' A' v).card ≤ D.card := (card_le_card hCD).trans card_image_le
  obtain ⟨j0, hj0, hne0⟩ := hne
  refine no_cycle_half_fold_count r' A' (2 * e + 1) g hr' hq he v hv1 hsum hbal hx
    (card_pos.mpr ⟨j0, mem_filter.mpr ⟨mem_range.mpr hj0, hne0⟩⟩)
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ hcard) hDg)

section Cycle
open CollatzProof

/-- **Cycle form of T3c.** No positive `T`-cycle with `r = 2r'` odd steps and period `L = 2A'`
has an `h`-balanced valuation word (`h ≤ A'`) with between `1` and `< r'/g` bad columns,
when `(r' 2^{2h+1})^2 < 2^{3(g+1)}`. -/
theorem cycle_half_fold_count {m r' A' : ℕ} {v : ℕ → ℕ} (hr' : 1 ≤ r')
    (hv1 : ∀ i < 2 * r', 1 ≤ v i) (hL : psum v (2 * r') = 2 * A')
    (hodd : ∀ j < 2 * A', (T^[j] m % 2 = 1 ↔ ∃ i < 2 * r', psum v i = j))
    (hcyc : T^[2 * A'] m = m) (h g : ℕ) (hhA : h ≤ A')
    (hbal : ∀ i j, i ≤ j → j ≤ 2 * r' →
        (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * h ∧
        r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * h)
    (hx : (r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (hC0 : 0 < (badCols r' A' v).card) (hCg : (badCols r' A' v).card * g < r') : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_half_fold_count r' A' h g hr' hq hhA v hv1 hL hbal hx hC0 hCg hdiv

/-- **Cycle form of T3e.** No positive `T`-cycle with `r = 2r'` odd steps and period `L = 2A'`
has a valuation word that is not `r'`-periodic, stays within `e` of `chr r L` (`2e+1 ≤ A'`), and
deviates from it at a set `D` of indices with `|D|·g < r'`, where
`(r' 2^{2(2e+1)+1})^2 < 2^{3(g+1)}`. Non-vacuity: `r = 40902`, `L = 64830` (or `64832`), `e = 1`,
`g = 14`, so up to `|D| = 1460` deviating indices at arbitrary positions (`witness_fold`); e.g.
`v = chr r L` with height-one moves (e.g. right flips) at up to `1460` separated sites, not all
repeated `r'` indices later (so `v` is not `r'`-periodic). -/
theorem cycle_sites_even {m r' A' : ℕ} {v : ℕ → ℕ} (hr' : 1 ≤ r')
    (hv1 : ∀ i < 2 * r', 1 ≤ v i) (hL : psum v (2 * r') = 2 * A')
    (hodd : ∀ j < 2 * A', (T^[j] m % 2 = 1 ↔ ∃ i < 2 * r', psum v i = j))
    (hcyc : T^[2 * A'] m = m) (e g : ℕ) (he : 2 * e + 1 ≤ A')
    (hx : (r' * 2 ^ (2 * (2 * e + 1) + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (D : Finset ℕ) (hDg : D.card * g < r')
    (hout : ∀ j < 2 * r', j ∉ D → psum v j = psum (NormGoal.chr (2 * r') (2 * A')) j)
    (hup : ∀ j < 2 * r', psum v j ≤ psum (NormGoal.chr (2 * r') (2 * A')) j + e)
    (hdn : ∀ j < 2 * r', psum (NormGoal.chr (2 * r') (2 * A')) j ≤ psum v j + e)
    (hne : ∃ j < r', psum v (j + r') ≠ psum v j + A') : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_sites_even r' A' e g hr' hq he hx v hv1 hL D hDg hout hup hdn hne hdiv

end Cycle

/-- Non-vacuity certificate: at `r = 40902 = 2·20451`, `L = 64830 = 2·32415`,
`3^r + 1 < 2^L`, and with `e = 1`, `g = 14` the height hypothesis of `no_cycle_sites_even`
holds, so `|D| ≤ 1460` (`1460·14 < 20451`). -/
theorem witness_fold : 3 ^ (2 * 20451) + 1 < 2 ^ (2 * 32415) ∧
    (20451 * 2 ^ (2 * (2 * 1 + 1) + 1)) ^ 2 < 2 ^ (3 * (14 + 1)) ∧ 1460 * 14 < 20451 := by
  decide +kernel

/-- The same at `L = 64832 = 2·32416`, where `gcd(L, r) = 2` exactly. -/
theorem witness_fold2 : Nat.gcd 64832 40902 = 2 ∧ 3 ^ (2 * 20451) + 1 < 2 ^ (2 * 32416) ∧
    (20451 * 2 ^ (2 * (2 * 1 + 1) + 1)) ^ 2 < 2 ^ (3 * (14 + 1)) := by
  decide +kernel

/-! ## General `p = n + 1 ≥ 2` (T2) -/

theorem Sg_eq_sum (U V : ℕ) : ∀ n, (Sg U V n : ℤ) = ∑ u ∈ range n, (U : ℤ) ^ u * (V : ℤ) ^ (n - 1 - u)
  | 0 => by simp [Sg]
  | n + 1 => by
    rw [sum_range_succ']
    simp only [Sg]; push_cast; rw [Sg_eq_sum U V n, mul_sum, add_comm]
    congr 1
    · apply sum_congr rfl; intro u hu
      have := mem_range.mp hu
      rw [show n - (u + 1) = n - 1 - u by omega]; ring
    · simp

theorem sum_rows {M : Type*} [AddCommMonoid M] (G : ℕ → M) (r' : ℕ) :
    ∀ n, ∑ s ∈ range (n * r'), G s = ∑ u ∈ range n, ∑ c ∈ range r', G (c + u * r')
  | 0 => by simp
  | n + 1 => by
    rw [show (n + 1) * r' = n * r' + r' by ring, sum_range_add, sum_rows G r' n, sum_range_succ]
    congr 1; apply sum_congr rfl; intro c _; rw [add_comm]

theorem mod_div_of {r' c u s : ℕ} (hc : c < r') (hs : s = c + u * r') :
    s % r' = c ∧ s / r' = u := by
  subst hs; constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  · rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]

/-- Top-pivot fold exponents, in window coordinates `s < n r'` (`p = n + 1`). -/
def gα (n A' : ℕ) (E : ℕ → ℕ) (s : ℕ) : ℕ := E s + n * A'

def gβ (n r' A' : ℕ) (E : ℕ → ℕ) (s : ℕ) : ℕ := E (s % r' + n * r') + s / r' * A'

/-- **Top-pivot fold identity (any `p = n + 1`).** For every `E : ℕ → ℕ`, with
`Φ = Sg (2^{A'}) (3^{r'}) (n+1) = Σ_{u ≤ n} U^u V^{n-u}`:
`Φ ∣ U^n Σ_{s<(n+1)r'} 3^{(n+1)r'-1-s} 2^{E s} - Σ_{s<n r'} 3^{(n+1)r'-1-s}(2^{α_s} - 2^{β_s})`,
`α_s = E s + nA'`, `β_s = E(s mod r' + n r') + ⌊s/r'⌋ A'` (the pivot of the column of `s` is
the last row). Pure algebra. -/
theorem fold_top (n r' A' : ℕ) (E : ℕ → ℕ) :
    ((Sg (2 ^ A') (3 ^ r') (n + 1) : ℕ) : ℤ) ∣ (2 : ℤ) ^ (n * A') *
      ∑ s ∈ range ((n + 1) * r'), (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ E s -
      ∑ s ∈ range (n * r'), (3 : ℤ) ^ ((n + 1) * r' - 1 - s) *
        ((2 : ℤ) ^ gα n A' E s - 2 ^ gβ n r' A' E s) := by
  set U : ℤ := 2 ^ A' with hU
  set V : ℤ := 3 ^ r' with hV
  set N : ℤ := ∑ c ∈ range r', (3 : ℤ) ^ (r' - 1 - c) * 2 ^ E (c + n * r') with hN
  refine ⟨N, ?_⟩
  have hsplit : ∑ s ∈ range ((n + 1) * r'), (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ E s =
      ∑ s ∈ range (n * r'), (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ E s + N := by
    rw [show (n + 1) * r' = n * r' + r' by ring, sum_range_add]
    congr 1; rw [hN]; apply sum_congr rfl; intro c hc
    have := mem_range.mp hc
    rw [show n * r' + r' - 1 - (n * r' + c) = r' - 1 - c by omega, add_comm (n * r') c]
  rw [hsplit, mul_add, mul_sum, add_sub_right_comm, ← sum_sub_distrib]
  have hterm : ∀ s ∈ range (n * r'), (2 : ℤ) ^ (n * A') * ((3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ E s) -
      (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * ((2 : ℤ) ^ gα n A' E s - 2 ^ gβ n r' A' E s) =
      (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ gβ n r' A' E s := by
    intro s _
    simp only [gα]; rw [pow_add]; ring
  rw [sum_congr rfl hterm]
  have hrows := sum_rows (fun s => (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ gβ n r' A' E s) r' n
  rw [hrows]
  have hinner : ∀ u ∈ range n, ∀ c ∈ range r',
      (3 : ℤ) ^ ((n + 1) * r' - 1 - (c + u * r')) * 2 ^ gβ n r' A' E (c + u * r') =
      U ^ u * V ^ (n - u) * ((3 : ℤ) ^ (r' - 1 - c) * 2 ^ E (c + n * r')) := by
    intro u hu c hc
    have hu' := mem_range.mp hu
    have hc' := mem_range.mp hc
    obtain ⟨h1, h2⟩ := mod_div_of (s := c + u * r') hc' rfl
    simp only [gβ]; rw [h1, h2]
    obtain ⟨d, rfl⟩ : ∃ d, n = u + 1 + d := ⟨n - u - 1, by omega⟩
    have e3 : (u + 1 + d + 1) * r' - 1 - (c + u * r') = (r' - 1 - c) + r' * (u + 1 + d - u) := by
      rw [show u + 1 + d - u = d + 1 by omega]
      have e : (u + 1 + d + 1) * r' = u * r' + d * r' + r' + r' := by ring
      have e2 : r' * (d + 1) = d * r' + r' := by ring
      omega
    rw [e3, pow_add, pow_add, hU, hV, ← pow_mul, ← pow_mul]; ring
  rw [sum_congr rfl (fun u hu => sum_congr rfl (hinner u hu)), sum_comm]
  have hL : ∑ c ∈ range r', ∑ u ∈ range n, U ^ u * V ^ (n - u) *
      ((3 : ℤ) ^ (r' - 1 - c) * 2 ^ E (c + n * r')) = (∑ u ∈ range n, U ^ u * V ^ (n - u)) * N := by
    rw [hN, mul_sum]; apply sum_congr rfl; intro c _; rw [sum_mul]
  have hS : ((Sg (2 ^ A') (3 ^ r') (n + 1) : ℕ) : ℤ) = ∑ u ∈ range n, U ^ u * V ^ (n - u) + U ^ n := by
    rw [Sg_eq_sum, sum_range_succ, show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
    push_cast
    rw [hU, hV]
  rw [hL, hS, show (2 : ℤ) ^ (n * A') = U ^ n by rw [hU, ← pow_mul, mul_comm]]
  ring

theorem mono_of_succ {E : ℕ → ℕ} {M : ℕ} (hE : ∀ s, s < M → E s < E (s + 1)) :
    ∀ s t, s ≤ t → t ≤ M → E s ≤ E t := by
  intro s t hst htM
  induction t with
  | zero => have : s = 0 := by omega
            rw [this]
  | succ t ih =>
    rcases eq_or_lt_of_le hst with h | h
    · rw [h]
    · have := ih (by omega) (by omega); have := hE t (by omega); omega

/-- **Fold core (any `p = n + 1 ≥ 2`), in window coordinates.** Let `E` be strictly increasing on
`[0, (n+1) r']` with `E((n+1)r') = E 0 + (n+1)A'`, *column `0` good* (`E(n r') = E 0 + n A'`),
two-sided `h`-balanced (`h ≤ A'`), and let `Φ = Sg (2^{A'}) (3^{r'}) (n+1)` (odd, prime to `3`)
divide `Σ_{s<(n+1)r'} 3^{(n+1)r'-1-s} 2^{E s}`. If the non-pivot indices `s < n r'` with
`α_s ≠ β_s` (see `fold_top`) all lie in `[a, a+w)` (`a + w ≤ n r'`), there is at least one, and
`(w 2^{2h+1})^{r'} 2^{(w-1)A'} < 2^{nA' r'}`, we get a contradiction. -/
theorem fold_core (n r' A' h a w : ℕ) (hn : 1 ≤ n) (hr : 0 < r') (h3 : 3 ^ r' ≤ 2 ^ A')
    (hhA : h ≤ A') (E : ℕ → ℕ) (hE : ∀ s, s < (n + 1) * r' → E s < E (s + 1))
    (hper : E ((n + 1) * r') = E 0 + (n + 1) * A') (hcol0 : E (n * r') = E 0 + n * A')
    (hbal : ∀ s t, s ≤ t → t ≤ (n + 1) * r' →
        (t - s) * A' ≤ r' * (E t - E s) + r' * h ∧ r' * (E t - E s) ≤ (t - s) * A' + r' * h)
    (haw : a + w ≤ n * r')
    (hW : (w * 2 ^ (2 * h + 1)) ^ r' * 2 ^ ((w - 1) * A') < 2 ^ (n * A' * r'))
    (hout : ∀ s < n * r', (s < a ∨ a + w ≤ s) → gα n A' E s = gβ n r' A' E s)
    (hne : ∃ s, a ≤ s ∧ s < a + w ∧ gα n A' E s ≠ gβ n r' A' E s)
    (hΦ2 : Nat.Coprime 2 (Sg (2 ^ A') (3 ^ r') (n + 1)))
    (hΦ3 : Nat.Coprime 3 (Sg (2 ^ A') (3 ^ r') (n + 1)))
    (hdvd : ((Sg (2 ^ A') (3 ^ r') (n + 1) : ℕ) : ℤ) ∣
      ∑ s ∈ range ((n + 1) * r'), (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ E s) : False := by
  set Φ := Sg (2 ^ A') (3 ^ r') (n + 1) with hΦ
  have hΦ3' : IsCoprime (Φ : ℤ) (3 : ℤ) := by
    have := Nat.isCoprime_iff_coprime.mpr hΦ3.symm; simpa using this
  set T : ℕ → ℤ := fun s => (3 : ℤ) ^ ((n + 1) * r' - 1 - s) *
    ((2 : ℤ) ^ gα n A' E s - 2 ^ gβ n r' A' E s) with hT
  have hF : (Φ : ℤ) ∣ ∑ s ∈ range (n * r'), T s := by
    have h1 := fold_top n r' A' E
    have h2 : (Φ : ℤ) ∣ (2 : ℤ) ^ (n * A') *
        ∑ s ∈ range ((n + 1) * r'), (3 : ℤ) ^ ((n + 1) * r' - 1 - s) * 2 ^ E s :=
      dvd_mul_of_dvd_right hdvd _
    have := dvd_sub h2 h1
    simpa using this
  have hrr : n * r' < (n + 1) * r' := by
    rw [add_mul, one_mul]; omega
  have hX : (Φ : ℤ) ∣ ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ gα n A' E (a + s) - 2 ^ gβ n r' A' E (a + s)) := by
    have hsplit : ∑ s ∈ range (n * r'), T s = ∑ s ∈ range a, T s +
        (∑ s ∈ range w, T (a + s) + ∑ s ∈ range (n * r' - a - w), T (a + w + s)) := by
      have e : n * r' = a + (w + (n * r' - a - w)) := by omega
      conv_lhs => rw [e]
      rw [sum_range_add, sum_range_add]
      congr 2; apply sum_congr rfl; intro s _; rw [add_assoc]
    have hz1 : ∑ s ∈ range a, T s = 0 := by
      apply sum_eq_zero; intro s hs; have := mem_range.mp hs
      simp only [hT]; rw [hout s (by omega) (Or.inl this), sub_self, mul_zero]
    have hz2 : ∑ s ∈ range (n * r' - a - w), T (a + w + s) = 0 := by
      apply sum_eq_zero; intro s hs; have := mem_range.mp hs
      simp only [hT]; rw [hout (a + w + s) (by omega) (Or.inr (by omega)), sub_self, mul_zero]
    have hw3 : ∑ s ∈ range w, T (a + s) = 3 ^ ((n + 1) * r' - a - w) *
        ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
          ((2 : ℤ) ^ gα n A' E (a + s) - 2 ^ gβ n r' A' E (a + s)) := by
      rw [mul_sum]; apply sum_congr rfl; intro s hs
      have := mem_range.mp hs
      simp only [hT]; rw [← mul_assoc, ← pow_add]; congr 2; omega
    rw [hsplit, hz1, hz2, zero_add, add_zero, hw3] at hF
    exact (hΦ3'.pow_right).dvd_of_dvd_mul_left hF
  have hEle := mono_of_succ hE
  -- decomposition of window indices
  have hdec : ∀ s, s < n * r' → s % r' < r' ∧ s / r' < n ∧ s = s % r' + s / r' * r' := by
    intro s hs
    refine ⟨Nat.mod_lt _ hr, ?_, (Nat.mod_add_div' s r').symm⟩
    exact (Nat.div_lt_iff_lt_mul hr).mpr hs
  set m := E a + n * A' - h with hm
  have hnA : A' ≤ n * A' := Nat.le_mul_of_pos_left _ hn
  refine window_pair (r := r') (A := A') (E := n * A') (H := 2 * h + 1) (w := w) (m := m)
    (S := Φ) hr h3 hΦ2 ?_ hW (fun s => gα n A' E (a + s)) (fun s => gβ n r' A' E (a + s))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hX
  · rw [hΦ, mul_comm, pow_mul]; exact pow_le_Sg _ _ _
  · intro s hs; simp only [gα]
    have := hE (a + s) (by omega); rw [show a + (s + 1) = a + s + 1 by ring]; omega
  · intro s hs; simp only [gβ]
    obtain ⟨hc, hu, hsd⟩ := hdec (a + s) (by omega)
    set c := (a + s) % r'; set u := (a + s) / r'
    by_cases hc1 : c + 1 < r'
    · obtain ⟨e1, e2⟩ := mod_div_of (s := a + (s + 1)) (u := u) hc1 (by omega)
      rw [e1, e2]
      have : c + n * r' < (n + 1) * r' := by rw [add_mul, one_mul]; omega
      have := hE (c + n * r') this
      rw [show c + 1 + n * r' = c + n * r' + 1 by ring]; omega
    · obtain ⟨e1, e2⟩ := mod_div_of (s := a + (s + 1)) (c := 0) (u := u + 1) hr
        (by rw [add_mul, one_mul]; omega)
      rw [e1, e2, zero_add, hcol0]
      have hlast : c + n * r' + 1 = (n + 1) * r' := by rw [add_mul, one_mul]; omega
      have := hE (c + n * r') (by omega)
      rw [hlast, hper] at this
      have : (u + 1) * A' = u * A' + A' := by ring
      have : (n + 1) * A' = n * A' + A' := by ring
      omega
  · intro s hs; simp only [gα]; have := hEle a (a + s) (by omega) (by omega); omega
  · intro s hs; simp only [gβ]
    obtain ⟨hc, hu, hsd⟩ := hdec (a + s) (by omega)
    set c := (a + s) % r'; set u := (a + s) / r'
    have hKr : (n - u) * r' + u * r' = n * r' := by rw [← add_mul, Nat.sub_add_cancel hu.le]
    have hKA : (n - u) * A' + u * A' = n * A' := by rw [← add_mul, Nat.sub_add_cancel hu.le]
    have hTa : c + n * r' - a = s + (n - u) * r' := by omega
    have hb := (hbal a (c + n * r') (by omega) (by rw [add_mul, one_mul]; omega)).1
    rw [hTa] at hb
    have hle := hEle a (c + n * r') (by omega) (by rw [add_mul, one_mul]; omega)
    set D := E (c + n * r') - E a
    have e1 : (s + (n - u) * r') * A' = s * A' + r' * ((n - u) * A') := by ring
    have e2 := mul_add r' D h
    have : r' * ((n - u) * A') ≤ r' * (D + h) := by
      have := Nat.zero_le (s * A'); omega
    have := Nat.le_of_mul_le_mul_left this hr
    omega
  · intro s hs; simp only [gα]
    have hb := (hbal a (a + s) (by omega) (by omega)).2
    rw [show a + s - a = s by omega] at hb
    have hle := hEle a (a + s) (by omega) (by omega)
    have := floor_up hr hb
    omega
  · intro s hs; simp only [gβ]
    obtain ⟨hc, hu, hsd⟩ := hdec (a + s) (by omega)
    set c := (a + s) % r'; set u := (a + s) / r'
    have hKr : (n - u) * r' + u * r' = n * r' := by rw [← add_mul, Nat.sub_add_cancel hu.le]
    have hKA : (n - u) * A' + u * A' = n * A' := by rw [← add_mul, Nat.sub_add_cancel hu.le]
    have hTa : c + n * r' - a = s + (n - u) * r' := by omega
    have hb := (hbal a (c + n * r') (by omega) (by rw [add_mul, one_mul]; omega)).2
    rw [hTa] at hb
    have hle := hEle a (c + n * r') (by omega) (by rw [add_mul, one_mul]; omega)
    set D := E (c + n * r') - E a
    have e1 : (s + (n - u) * r') * A' = s * A' + r' * ((n - u) * A') := by ring
    have e2 := mul_add r' ((n - u) * A') h
    have := floor_up (x := D) (y := s * A') (h := (n - u) * A' + h) hr (by omega)
    omega
  · obtain ⟨s, h1, h2, h3⟩ := hne
    exact ⟨s - a, by omega, by rw [show a + (s - a) = s by omega]; exact h3⟩

/-- **Rotation fold.** For `k ≤ R`, with `ext` the extension `a_{j+R} = a_j + A`:
`Σ_{s<R} 3^{R-1-s} 2^{a_{k+s}} = 3^k B(v) + (2^A - 3^R) Σ_{i<k} 3^{k-1-i} 2^{a_i}`. -/
theorem rot_fold (R A k : ℕ) (hk : k ≤ R) (v : ℕ → ℕ) :
    ∑ s ∈ range R, (3 : ℤ) ^ (R - 1 - s) * 2 ^ ext R A v (k + s) =
      3 ^ k * (Bnum R v : ℤ) +
        ((2 : ℤ) ^ A - 3 ^ R) * ∑ i ∈ range k, (3 : ℤ) ^ (k - 1 - i) * 2 ^ psum v i := by
  rw [cast_Bnum]
  have hL : ∑ s ∈ range R, (3 : ℤ) ^ (R - 1 - s) * 2 ^ ext R A v (k + s) =
      3 ^ k * ∑ s ∈ range (R - k), (3 : ℤ) ^ (R - 1 - (k + s)) * 2 ^ psum v (k + s) +
      2 ^ A * ∑ i ∈ range k, (3 : ℤ) ^ (k - 1 - i) * 2 ^ psum v i := by
    have e := sum_range_add (fun s => (3 : ℤ) ^ (R - 1 - s) * 2 ^ ext R A v (k + s)) (R - k) k
    rw [Nat.sub_add_cancel hk] at e
    rw [e, mul_sum, mul_sum]
    congr 1
    · apply sum_congr rfl; intro s hs; have := mem_range.mp hs
      rw [ext_lt v (by omega), ← mul_assoc, ← pow_add]; congr 2; omega
    · apply sum_congr rfl; intro i hi; have := mem_range.mp hi
      rw [show k + (R - k + i) = i + R by omega, ext_add,
        show R - 1 - (R - k + i) = k - 1 - i by omega, pow_add]; ring
  have hB : ∑ i ∈ range R, (3 : ℤ) ^ (R - 1 - i) * 2 ^ psum v i =
      ∑ i ∈ range k, (3 : ℤ) ^ (R - 1 - i) * 2 ^ psum v i +
      ∑ s ∈ range (R - k), (3 : ℤ) ^ (R - 1 - (k + s)) * 2 ^ psum v (k + s) := by
    have e := sum_range_add (fun i => (3 : ℤ) ^ (R - 1 - i) * 2 ^ psum v i) k (R - k)
    rw [Nat.add_sub_cancel' hk] at e; exact e
  have hfold : (3 : ℤ) ^ k * ∑ i ∈ range k, (3 : ℤ) ^ (R - 1 - i) * 2 ^ psum v i =
      3 ^ R * ∑ i ∈ range k, (3 : ℤ) ^ (k - 1 - i) * 2 ^ psum v i := by
    rw [mul_sum, mul_sum]; apply sum_congr rfl; intro i hi; have := mem_range.mp hi
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
  rw [hL, hB]
  linear_combination (-1 : ℤ) * hfold

/-- General arc-size condition: if `3r' ≤ 2A'`, `w + g ≤ M r'`, `w ≤ W`, and
`(W 2^{2h+1})^2 < 2^{3(g+1)}`, then `(w 2^{2h+1})^{r'} 2^{(w-1)A'} < 2^{M A' r'}`. -/
theorem hW_gen {r' A' h g w W M : ℕ} (hr' : 0 < r') (h3 : 3 * r' ≤ 2 * A')
    (hwg : w + g ≤ M * r') (hwW : w ≤ W)
    (hx : (W * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1))) :
    (w * 2 ^ (2 * h + 1)) ^ r' * 2 ^ ((w - 1) * A') < 2 ^ (M * A' * r') := by
  rcases Nat.eq_zero_or_pos w with hw0 | hw0
  · rw [hw0, zero_mul, zero_pow (by omega), zero_mul]; positivity
  set x := W * 2 ^ (2 * h + 1) with hxdef
  have hxr : x ^ r' < 2 ^ ((g + 1) * A') := by
    have h2 : (x ^ r') ^ 2 < (2 ^ ((g + 1) * A')) ^ 2 := by
      calc (x ^ r') ^ 2 = (x ^ 2) ^ r' := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ < (2 ^ (3 * (g + 1))) ^ r' := Nat.pow_lt_pow_left hx (by omega)
        _ = 2 ^ ((g + 1) * (3 * r')) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ ((g + 1) * (2 * A')) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h3)
        _ = (2 ^ ((g + 1) * A')) ^ 2 := by rw [← pow_mul]; ring_nf
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h2
  have hle : (w * 2 ^ (2 * h + 1)) ^ r' ≤ x ^ r' :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hwW) _
  calc (w * 2 ^ (2 * h + 1)) ^ r' * 2 ^ ((w - 1) * A') ≤ x ^ r' * 2 ^ ((w - 1) * A') :=
        Nat.mul_le_mul_right _ hle
    _ < 2 ^ ((g + 1) * A') * 2 ^ ((w - 1) * A') :=
        Nat.mul_lt_mul_of_pos_right hxr (by positivity)
    _ = 2 ^ ((w + g) * A') := by
        rw [← pow_add, ← add_mul]; congr 2; omega
    _ ≤ 2 ^ (M * A' * r') := by
        apply Nat.pow_le_pow_right (by norm_num)
        calc (w + g) * A' ≤ M * r' * A' := Nat.mul_le_mul_right _ hwg
          _ = M * A' * r' := by ring

/-- The bad columns for general `p = n + 1`: `j < r'` with `P(j + t r') ≠ P j + t A'` for some
`t ≤ n`. -/
def badColsP (n r' A' : ℕ) (v : ℕ → ℕ) : Finset ℕ :=
  (range r').filter (fun j => ∃ t < n + 1, psum v (j + t * r') ≠ psum v j + t * A')

theorem three_le_of_hqP {n r' A' : ℕ} (hq : 3 ^ ((n + 1) * r') + 1 < 2 ^ ((n + 1) * A')) :
    3 ^ r' ≤ 2 ^ A' ∧ 3 * r' ≤ 2 * A' := by
  have h1 : 3 ^ r' ≤ 2 ^ A' := by
    by_contra h; push Not at h
    have : 2 ^ ((n + 1) * A') < 3 ^ ((n + 1) * r') := by
      rw [mul_comm, pow_mul, mul_comm, pow_mul]; exact Nat.pow_lt_pow_left h (by omega)
    omega
  refine ⟨h1, ?_⟩
  have h2 : 2 ^ (3 * r') ≤ 2 ^ (2 * A') := by
    calc 2 ^ (3 * r') = 8 ^ r' := by rw [pow_mul]; norm_num
      _ ≤ 9 ^ r' := Nat.pow_le_pow_left (by norm_num) _
      _ = (3 ^ r') ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (2 ^ A') ^ 2 := Nat.pow_le_pow_left h1 _
      _ = 2 ^ (2 * A') := by rw [← pow_mul, mul_comm]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- **T2: few bad columns, any common factor `p = n + 1 ≥ 2` of `r` and `A`.**
Let `r = (n+1) r'`, `A = (n+1) A'`, `3^r + 1 < 2^A`, and let `v` have entries `≥ 1` below `r`,
`psum v r = A`, two-sided `h`-balanced (`h ≤ A'`). Call column `j < r'` *bad* if
`P(j + t r') ≠ P j + t A'` for some `t ≤ n` (i.e. `v` is not `r'`-periodic there). If there are
between `1` and fewer than `r'/g` bad columns (`g ≥ 1`), and `(n r' 2^{2h+1})^2 < 2^{3(g+1)}`,
then `(2^A - 3^r) ∤ B(v)`. The bad columns may be anywhere. Proof: a free gap of `g` good columns
starts at `x` (`free_gap`); rotate to start at `x` (`rot_fold`, modulo `q`); fold modulo
`Φ = Σ_{u≤n} 2^{uA'} 3^{(n-u)r'}` (Solomon's `S_{n+1}` when `n+1 = gcd`) against the last row
(`fold_top`); `fold_core` (2-adic injectivity + size, `window_pair`) on the window
`[g, n r')`. -/
theorem no_cycle_fold_count (n r' A' h g : ℕ) (hn : 1 ≤ n) (hr' : 0 < r')
    (hq : 3 ^ ((n + 1) * r') + 1 < 2 ^ ((n + 1) * A')) (hhA : h ≤ A')
    (v : ℕ → ℕ) (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hsum : psum v ((n + 1) * r') = (n + 1) * A')
    (hbal : ∀ i j, i ≤ j → j ≤ (n + 1) * r' →
        (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * h ∧
        r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * h)
    (hg : 0 < g) (hx : (n * r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (hC0 : 0 < (badColsP n r' A' v).card) (hCg : (badColsP n r' A' v).card * g < r') :
    ¬ (2 ^ ((n + 1) * A') - 3 ^ ((n + 1) * r')) ∣ Bnum ((n + 1) * r') v := by
  intro hdiv
  obtain ⟨-, hΦ2, hΦ3, hΦq, -⟩ := solomon_factor (d := n + 1) (r' := r') (A' := A') (by omega) hr' hq
  obtain ⟨h3, h3r⟩ := three_le_of_hqP hq
  set R := (n + 1) * r' with hR
  set A := (n + 1) * A' with hA
  have hRr : R = n * r' + r' := by rw [hR]; ring
  have hAA : A = n * A' + A' := by rw [hA]; ring
  have hnr : r' ≤ n * r' := Nat.le_mul_of_pos_left _ hn
  set C := badColsP n r' A' v with hC
  have hCr : ∀ j ∈ C, j < r' := fun j hj => mem_range.mp (mem_filter.mp hj).1
  have hgr : g < r' := by
    have : 1 * g ≤ C.card * g := Nat.mul_le_mul_right _ hC0
    omega
  obtain ⟨x, hxr, hfree⟩ := free_gap r' g C hCr hCg
  -- good columns
  have hgood : ∀ j < r', j ∉ C → ∀ t < n + 1, psum v (j + t * r') = psum v j + t * A' := by
    intro j hj hjC t ht
    by_contra hne; exact hjC (mem_filter.mpr ⟨mem_range.mpr hj, t, ht, hne⟩)
  have hxC : x ∉ C := fun h => hfree x h (by unfold inArc; omega)
  set E : ℕ → ℕ := fun s => ext R A v (x + s) with hEdef
  have hp0 : psum v 0 = 0 := by simp [psum]
  -- E facts
  have hE : ∀ s, s < R → E s < E (s + 1) := by
    intro s hs
    simp only [hEdef]
    rcases lt_trichotomy (x + s + 1) R with h1 | h1 | h1
    · rw [ext_lt v (by omega), show x + (s + 1) = x + s + 1 by ring, ext_lt v h1]
      exact psum_lt hv1 (by omega) h1.le
    · have e0 := ext_add (r := R) (A := A) v 0
      rw [zero_add] at e0
      rw [ext_lt v (by omega), show x + (s + 1) = R by omega, e0, hp0, zero_add, ← hsum]
      exact psum_lt hv1 (by omega) le_rfl
    · obtain ⟨i, hi⟩ : ∃ i, x + s = i + R := ⟨x + s - R, by omega⟩
      rw [hi, show x + (s + 1) = (i + 1) + R by omega, ext_add, ext_add]
      have := psum_lt (v := v) hv1 (i := i) (j := i + 1) (by omega) (by omega); omega
  have hE0 : E 0 = psum v x := by simp only [hEdef]; rw [add_zero, ext_lt v (by omega)]
  have hper : E R = E 0 + A := by
    rw [hE0]; simp only [hEdef]; exact ext_add v x
  have hcol0 : E (n * r') = E 0 + n * A' := by
    rw [hE0]; simp only [hEdef]; rw [ext_lt v (by omega)]
    exact hgood x hxr hxC n (by omega)
  -- balance of E (cyclic)
  have hbalE : ∀ s t, s ≤ t → t ≤ R →
      (t - s) * A' ≤ r' * (E t - E s) + r' * h ∧ r' * (E t - E s) ≤ (t - s) * A' + r' * h := by
    intro s t hst htR
    simp only [hEdef]
    by_cases h1 : x + t < R
    · rw [ext_lt v h1, ext_lt v (by omega)]
      have := hbal (x + s) (x + t) (by omega) h1.le
      rwa [show x + t - (x + s) = t - s by omega] at this
    by_cases h2 : x + s < R
    · obtain ⟨i, hi⟩ : ∃ i, x + t = i + R := ⟨x + t - R, by omega⟩
      rw [hi, ext_add, ext_lt v h2]
      have hb := hbal i (x + s) (by omega) h2.le
      rw [show x + s - i = R - (t - s) by omega] at hb
      have hle := psum_le (v := v) hv1 (i := i) (j := x + s) (by omega) h2.le
      have hleA := psum_le (v := v) hv1 (i := x + s) (j := R) h2.le le_rfl
      rw [hsum] at hleA
      set Q := psum v (x + s) - psum v i
      have e1 : psum v i + A - psum v (x + s) = A - Q := by omega
      rw [e1]
      have e2 : (R - (t - s)) * A' + (t - s) * A' = r' * A := by
        rw [← add_mul, Nat.sub_add_cancel (by omega), hR, hA]; ring
      have e3 : r' * (A - Q) + r' * Q = r' * A := by
        rw [← mul_add, Nat.sub_add_cancel (by omega)]
      constructor <;> omega
    · obtain ⟨i, hi⟩ : ∃ i, x + t = i + R := ⟨x + t - R, by omega⟩
      obtain ⟨i', hi'⟩ : ∃ i', x + s = i' + R := ⟨x + s - R, by omega⟩
      rw [hi, hi', ext_add, ext_add]
      have := hbal i' i (by omega) (by omega)
      rw [show psum v i + A - (psum v i' + A) = psum v i - psum v i' by omega,
        show t - s = i - i' by omega]
      exact this
  -- divisibility of the rotated numerator
  have hΦB : ((Sg (2 ^ A') (3 ^ r') (n + 1) : ℕ) : ℤ) ∣ (Bnum R v : ℤ) :=
    Int.natCast_dvd_natCast.mpr (dvd_trans hΦq hdiv)
  have hΦq' : ((Sg (2 ^ A') (3 ^ r') (n + 1) : ℕ) : ℤ) ∣ (2 : ℤ) ^ A - 3 ^ R := by
    have := Int.natCast_dvd_natCast.mpr hΦq
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; exact this
  have hdvd : ((Sg (2 ^ A') (3 ^ r') (n + 1) : ℕ) : ℤ) ∣
      ∑ s ∈ range R, (3 : ℤ) ^ (R - 1 - s) * 2 ^ E s := by
    simp only [hEdef]
    rw [rot_fold R A x (by omega) v]
    exact dvd_add (dvd_mul_of_dvd_right hΦB _) (dvd_mul_of_dvd_left hΦq' _)
  -- window columns versus original columns
  have hcolE : ∀ c < r', (∀ t < n + 1, psum v ((if x + c < r' then x + c else x + c - r') + t * r') =
        psum v (if x + c < r' then x + c else x + c - r') + t * A') ↔
      (∀ u ≤ n, E (c + u * r') = E c + u * A') := by
    intro c hc
    have hEc : ∀ u ≤ n, E (c + u * r') = ext R A v (x + c + u * r') := by
      intro u hu; simp only [hEdef]; rw [add_assoc]
    split_ifs with h1
    · have hidx : ∀ u ≤ n, x + c + u * r' < R := by
        intro u hu; have := Nat.mul_le_mul_right r' hu; omega
      constructor
      · intro H u hu
        rw [hEc u hu, ext_lt v (hidx u hu)]
        have := hEc 0 (by omega); simp only [zero_mul, add_zero] at this
        rw [this, ext_lt v (by omega)]
        exact H u (by omega)
      · intro H t ht
        have := H t (by omega)
        rw [hEc t (by omega), ext_lt v (hidx t (by omega))] at this
        have h0 := hEc 0 (by omega); simp only [zero_mul, add_zero] at h0
        rw [h0, ext_lt v (by omega)] at this
        exact this
    · set j := x + c - r' with hj
      have hidx : ∀ u < n, x + c + u * r' = j + (u + 1) * r' := by
        intro u hu; have : (u + 1) * r' = u * r' + r' := by ring
        omega
      have hidx2 : ∀ u < n, j + (u + 1) * r' < R := by
        intro u hu; have := Nat.mul_le_mul_right r' (show u + 1 ≤ n by omega); omega
      have hlast : x + c + n * r' = j + R := by omega
      have hE0' : E c = psum v (j + r') := by
        have := hEc 0 (by omega); simp only [zero_mul, add_zero] at this
        rw [this, show x + c = j + 1 * r' by omega, ext_lt v (by omega)]; simp
      constructor
      · intro H u hu
        rw [hE0']
        have H1 := H 1 (by omega); simp only [one_mul] at H1
        rcases lt_or_eq_of_le hu with hu' | hu'
        · rw [hEc u hu, hidx u hu', ext_lt v (hidx2 u hu'), H (u + 1) (by omega), H1]; ring
        · rw [hu', hEc n le_rfl, hlast, ext_add, H1, hA]; ring
      · intro H t ht
        have Hn := H n le_rfl
        rw [hEc n le_rfl, hlast, ext_add, hE0'] at Hn
        have hj1 : psum v (j + r') = psum v j + A' := by rw [hAA] at Hn; omega
        rcases Nat.eq_zero_or_pos t with ht0 | ht0
        · rw [ht0]; simp
        · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
          have Hu := H u (by omega)
          rw [hEc u (by omega), hidx u (by omega), ext_lt v (hidx2 u (by omega)), hE0', hj1] at Hu
          rw [Hu]; ring
  have hαβ : ∀ c < r', ∀ u < n, gα n A' E (c + u * r') = E (c + u * r') + n * A' ∧
      gβ n r' A' E (c + u * r') = E (c + n * r') + u * A' := by
    intro c hc u hu
    obtain ⟨e1, e2⟩ := mod_div_of (s := c + u * r') (u := u) hc rfl
    exact ⟨rfl, by simp only [gβ]; rw [e1, e2]⟩
  refine fold_core n r' A' h g (n * r' - g) hn hr' h3 hhA E hE hper hcol0 hbalE (by omega)
    (hW_gen (W := n * r') hr' h3r (by omega) (by omega) hx) ?_ ?_ hΦ2 hΦ3 hdvd
  · intro s hs hs'
    have hsg : s < g := by omega
    obtain ⟨e1, e2⟩ := hαβ s (by omega) 0 (by omega)
    simp only [zero_mul, add_zero] at e1 e2
    rw [e1, e2]
    have hjg : (if x + s < r' then x + s else x + s - r') ∉ C := by
      intro hm; apply hfree _ hm; unfold inArc; split_ifs <;> omega
    have := (hcolE s (by omega)).mp (hgood _ (by split_ifs <;> omega) hjg) n le_rfl
    rw [this]
  · obtain ⟨j0, hj0⟩ := card_pos.mp hC0
    have hj0r := hCr j0 hj0
    have hj0g := hfree j0 hj0
    set c0 := if x ≤ j0 then j0 - x else j0 + r' - x with hc0
    have hc0r : c0 < r' := by rw [hc0]; split_ifs <;> omega
    have hc0g : g ≤ c0 := by unfold inArc at hj0g; rw [hc0]; split_ifs <;> omega
    have hjc : (if x + c0 < r' then x + c0 else x + c0 - r') = j0 := by
      rw [hc0]; split_ifs <;> omega
    by_contra hall
    push Not at hall
    have hEg : ∀ u ≤ n, E (c0 + u * r') = E c0 + u * A' := by
      have h0 := hall c0 hc0g (by omega)
      obtain ⟨e1, e2⟩ := hαβ c0 hc0r 0 (by omega)
      simp only [zero_mul, add_zero] at e1 e2 h0
      rw [e1, e2] at h0
      intro u hu
      rcases lt_or_eq_of_le hu with hu' | hu'
      · have hu2 := hall (c0 + u * r') (by omega)
          (by have := Nat.mul_le_mul_right r' (show u + 1 ≤ n by omega)
              rw [add_mul, one_mul] at this; omega)
        obtain ⟨f1, f2⟩ := hαβ c0 hc0r u hu'
        rw [f1, f2] at hu2
        omega
      · rw [hu']; omega
    have := (hcolE c0 hc0r).mpr hEg
    rw [hjc] at this
    obtain ⟨t, ht, hne⟩ := (mem_filter.mp hj0).2
    exact hne (this t ht)

/-- `bal_of_chr` for any length `N`. -/
theorem bal_of_chr_gen {N r' A' e : ℕ} (hr' : 0 < r') (v : ℕ → ℕ) (hv1 : ∀ i < N, 1 ≤ v i)
    (hup : ∀ j ≤ N, psum v j ≤ j * A' / r' + e)
    (hdn : ∀ j ≤ N, j * A' / r' ≤ psum v j + e) :
    ∀ i j, i ≤ j → j ≤ N →
        (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * (2 * e + 1) ∧
        r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * (2 * e + 1) := by
  intro i j hij hj
  have hle := psum_le hv1 hij hj
  have ui := hup i (by omega); have uj := hup j hj
  have di := hdn i (by omega); have dj := hdn j hj
  set Pi := psum v i; set Pj := psum v j
  set ci := i * A' / r'; set cj := j * A' / r'
  have hci1 : ci * r' ≤ i * A' := Nat.div_mul_le_self _ _
  have hcj1 : cj * r' ≤ j * A' := Nat.div_mul_le_self _ _
  have hci2 : i * A' < ci * r' + r' := Nat.lt_div_mul_add hr'
  have hcj2 : j * A' < cj * r' + r' := Nat.lt_div_mul_add hr'
  have m1 : r' * Pj ≤ r' * cj + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ uj
  have m2 : r' * cj ≤ r' * Pj + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ dj
  have m3 : r' * Pi ≤ r' * ci + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ ui
  have m4 : r' * ci ≤ r' * Pi + r' * e := by rw [← mul_add]; exact Nat.mul_le_mul_left _ di
  have hia : i * A' ≤ j * A' := Nat.mul_le_mul_right _ hij
  have hPP : r' * Pi ≤ r' * Pj := Nat.mul_le_mul_left _ hle
  have e1 : r' * (2 * e + 1) = 2 * (r' * e) + r' := by ring
  rw [mul_comm ci r'] at hci1 hci2
  rw [mul_comm cj r'] at hcj1 hcj2
  rw [Nat.sub_mul, Nat.mul_sub, e1]
  constructor <;> omega

theorem psum_chr_mul {n r' A' : ℕ} (j : ℕ) :
    psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j = j * A' / r' := by
  rw [psum_chr, show j * ((n + 1) * A') = (n + 1) * (j * A') by ring]
  exact Nat.mul_div_mul_left _ _ (by omega)

/-- **T3 for any `p = n + 1 ≥ 2`: few deviating sites from chr, any positions.**
Let `r = (n+1) r'`, `A = (n+1) A'`, `3^r + 1 < 2^A`, `2e + 1 ≤ A'`, `g ≥ 1`, and
`(n r' 2^{2(2e+1)+1})^2 < 2^{3(g+1)}`. Let `v` have entries `≥ 1`, `psum v r = A`, partial sums
within `e` of those of `chr r A`, equal to them outside a set `D` with `|D|·g < r'`. If `v` is
not `r'`-periodic, then `(2^A - 3^r) ∤ B(v)`. -/
theorem no_cycle_sites_fold (n r' A' e g : ℕ) (hn : 1 ≤ n) (hr' : 0 < r')
    (hq : 3 ^ ((n + 1) * r') + 1 < 2 ^ ((n + 1) * A')) (he : 2 * e + 1 ≤ A') (hg : 0 < g)
    (hx : (n * r' * 2 ^ (2 * (2 * e + 1) + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (v : ℕ → ℕ) (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hsum : psum v ((n + 1) * r') = (n + 1) * A')
    (D : Finset ℕ) (hDg : D.card * g < r')
    (hout : ∀ j < (n + 1) * r', j ∉ D →
      psum v j = psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j)
    (hup : ∀ j < (n + 1) * r', psum v j ≤ psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j + e)
    (hdn : ∀ j < (n + 1) * r', psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j ≤ psum v j + e)
    (hne : ∃ j < r', ∃ t < n + 1, psum v (j + t * r') ≠ psum v j + t * A') :
    ¬ (2 ^ ((n + 1) * A') - 3 ^ ((n + 1) * r')) ∣ Bnum ((n + 1) * r') v := by
  have hc : ∀ j, psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j = j * A' / r' :=
    fun j => psum_chr_mul j
  have hend : (n + 1) * r' * A' / r' = (n + 1) * A' := by
    rw [mul_assoc, mul_comm r' A', ← mul_assoc, Nat.mul_div_cancel _ hr']
  have hup' : ∀ j ≤ (n + 1) * r', psum v j ≤ j * A' / r' + e := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · rw [← hc]; exact hup j h
    · rw [h, hsum, hend]; omega
  have hdn' : ∀ j ≤ (n + 1) * r', j * A' / r' ≤ psum v j + e := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · rw [← hc]; exact hdn j h
    · rw [h, hsum, hend]; omega
  have hbal := bal_of_chr_gen hr' v hv1 hup' hdn'
  have hCD : badColsP n r' A' v ⊆ D.image (fun i => i % r') := by
    intro j hj
    obtain ⟨hj1, t, ht, hne'⟩ := mem_filter.mp hj
    have hj1 := mem_range.mp hj1
    rw [mem_image]
    by_cases hjD : j ∈ D
    · exact ⟨j, hjD, Nat.mod_eq_of_lt hj1⟩
    by_cases hjD' : j + t * r' ∈ D
    · exact ⟨j + t * r', hjD', by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj1]⟩
    exfalso; apply hne'
    have hlt : j + t * r' < (n + 1) * r' := by
      have := Nat.mul_le_mul_right r' (show t ≤ n by omega)
      rw [add_mul, one_mul]; omega
    rw [hout j (by omega) hjD, hout (j + t * r') hlt hjD', hc, hc, add_mul, mul_assoc,
      mul_comm r' A', ← mul_assoc, Nat.add_mul_div_right _ _ hr']
  have hcard : (badColsP n r' A' v).card ≤ D.card := (card_le_card hCD).trans card_image_le
  obtain ⟨j0, hj0, t0, ht0, hne0⟩ := hne
  refine no_cycle_fold_count n r' A' (2 * e + 1) g hn hr' hq he v hv1 hsum hbal hg hx
    (card_pos.mpr ⟨j0, mem_filter.mpr ⟨mem_range.mpr hj0, t0, ht0, hne0⟩⟩)
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ hcard) hDg)

section CycleP
open CollatzProof

/-- **Cycle form of T2.** No positive `T`-cycle with `r = (n+1) r'` odd steps and period
`L = (n+1) A'` (`n ≥ 1`) has an `h`-balanced valuation word (`h ≤ A'`) with between `1` and
fewer than `r'/g` bad columns (`g ≥ 1`), when `(n r' 2^{2h+1})^2 < 2^{3(g+1)}`. -/
theorem cycle_fold_count {m n r' A' : ℕ} {v : ℕ → ℕ} (hn : 1 ≤ n) (hr' : 1 ≤ r')
    (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hL : psum v ((n + 1) * r') = (n + 1) * A')
    (hodd : ∀ j < (n + 1) * A', (T^[j] m % 2 = 1 ↔ ∃ i < (n + 1) * r', psum v i = j))
    (hcyc : T^[(n + 1) * A'] m = m) (h g : ℕ) (hhA : h ≤ A')
    (hbal : ∀ i j, i ≤ j → j ≤ (n + 1) * r' →
        (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * h ∧
        r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * h)
    (hg : 0 < g) (hx : (n * r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (hC0 : 0 < (badColsP n r' A' v).card) (hCg : (badColsP n r' A' v).card * g < r') : False := by
  have h2 : 2 ≤ (n + 1) * r' := by
    have := Nat.mul_le_mul hn hr'; rw [add_mul, one_mul]; omega
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q h2 hv1 hL hodd hcyc
  exact no_cycle_fold_count n r' A' h g hn hr' hq hhA v hv1 hL hbal hg hx hC0 hCg hdiv

/-- **Cycle form of T3 (any `p = n + 1 ≥ 2`).** No positive `T`-cycle with `r = (n+1) r'` odd
steps and period `L = (n+1) A'` has a valuation word that is not `r'`-periodic, stays within `e`
of `chr r L` (`2e + 1 ≤ A'`), and deviates from it at a set `D` of indices with `|D|·g < r'`,
where `(n r' 2^{2(2e+1)+1})^2 < 2^{3(g+1)}`, `g ≥ 1`. Non-vacuity (`witness_fold3`,
`witness_fold4`): `r = 122703`, `L = 194484` (`p = 3`, `e = 1`, `g = 15`, `|D| ≤ 2726`) and
`r = 122704`, `L = 194484` (`p = 4`, `|D| ≤ 2045`). -/
theorem cycle_sites_fold {m n r' A' : ℕ} {v : ℕ → ℕ} (hn : 1 ≤ n) (hr' : 1 ≤ r')
    (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hL : psum v ((n + 1) * r') = (n + 1) * A')
    (hodd : ∀ j < (n + 1) * A', (T^[j] m % 2 = 1 ↔ ∃ i < (n + 1) * r', psum v i = j))
    (hcyc : T^[(n + 1) * A'] m = m) (e g : ℕ) (he : 2 * e + 1 ≤ A') (hg : 0 < g)
    (hx : (n * r' * 2 ^ (2 * (2 * e + 1) + 1)) ^ 2 < 2 ^ (3 * (g + 1)))
    (D : Finset ℕ) (hDg : D.card * g < r')
    (hout : ∀ j < (n + 1) * r', j ∉ D →
      psum v j = psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j)
    (hup : ∀ j < (n + 1) * r', psum v j ≤ psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j + e)
    (hdn : ∀ j < (n + 1) * r', psum (NormGoal.chr ((n + 1) * r') ((n + 1) * A')) j ≤ psum v j + e)
    (hne : ∃ j < r', ∃ t < n + 1, psum v (j + t * r') ≠ psum v j + t * A') : False := by
  have h2 : 2 ≤ (n + 1) * r' := by
    have := Nat.mul_le_mul hn hr'; rw [add_mul, one_mul]; omega
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q h2 hv1 hL hodd hcyc
  exact no_cycle_sites_fold n r' A' e g hn hr' hq he hg hx v hv1 hL D hDg hout hup hdn hne hdiv

end CycleP

/-- Non-vacuity, `p = 3`: `r = 122703 = 3·40901`, `L = 194484 = 3·64828`, `3^r + 1 < 2^L`,
and with `e = 1`, `g = 15` the hypothesis of `no_cycle_sites_fold` holds; `|D| ≤ 2726`. -/
theorem witness_fold3 : 3 ^ ((2 + 1) * 40901) + 1 < 2 ^ ((2 + 1) * 64828) ∧
    (2 * 40901 * 2 ^ (2 * (2 * 1 + 1) + 1)) ^ 2 < 2 ^ (3 * (15 + 1)) ∧ 2726 * 15 < 40901 := by
  decide +kernel

/-- Non-vacuity, `p = 4`: `r = 122704 = 4·30676`, `L = 194484 = 4·48621`; `e = 1`, `g = 15`,
`|D| ≤ 2045`. -/
theorem witness_fold4 : 3 ^ ((3 + 1) * 30676) + 1 < 2 ^ ((3 + 1) * 48621) ∧
    (3 * 30676 * 2 ^ (2 * (2 * 1 + 1) + 1)) ^ 2 < 2 ^ (3 * (15 + 1)) ∧ 2045 * 15 < 30676 := by
  decide +kernel

end Collatz.NormFold

#print axioms Collatz.NormFold.window_pair
#print axioms Collatz.NormFold.fold_two
#print axioms Collatz.NormFold.no_cycle_half_fold
#print axioms Collatz.NormFold.hW_fold
#print axioms Collatz.NormFold.no_cycle_half_fold_count
#print axioms Collatz.NormFold.bal_of_chr
#print axioms Collatz.NormFold.no_cycle_sites_even
#print axioms Collatz.NormFold.cycle_half_fold_count
#print axioms Collatz.NormFold.cycle_sites_even
#print axioms Collatz.NormFold.witness_fold
#print axioms Collatz.NormFold.witness_fold2
#print axioms Collatz.NormFold.fold_top
#print axioms Collatz.NormFold.rot_fold
#print axioms Collatz.NormFold.fold_core
#print axioms Collatz.NormFold.no_cycle_fold_count
#print axioms Collatz.NormFold.no_cycle_sites_fold
#print axioms Collatz.NormFold.cycle_fold_count
#print axioms Collatz.NormFold.cycle_sites_fold
#print axioms Collatz.NormFold.witness_fold3
#print axioms Collatz.NormFold.witness_fold4
