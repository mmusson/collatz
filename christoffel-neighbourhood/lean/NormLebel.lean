import NormShiftSlide

/-!
# divisor-level shift lift; Lebel's single-prime Conjecture 11.1 above `D^{2/3}`

Notation as in `NormShift`: `D = q = 2^A - 3^r`, `B(v)` the Böhm–Sontacchi numerator, `chr r A`
the lower Christoffel word, `ε_ρ = psum v ρ - ⌊ρA/r⌋`.

**Observation.** The `NormShift` shift lift (`NormShift.shift_lift`) uses `q` only through
`Q ∣ G a` (rotation numerators), `gcd(Q, 6) = 1` and `|N| < Q ⇒ N = 0`; all three hold for
ANY divisor `Q` of `q`.

* `shift_lift_dvd` (T1): the shift lift for any divisor `Q ∣ 2^A - 3^r`, size hypothesis
  `(r 2^E)^r 2^{A(r-1-g)+r} < Q^r`. `free_points`: `|X| g < r` leaves a free cyclic window.
* `one_move_dvd` (T2): coprime `(A, r)`, `r ≥ 2`: any divisor `Q` of `D` with
  `(8r)^r 2^{A(r-1-⌊(r-1)/3⌋)+r} < Q^r` (roughly `Q > 16r·D^{2/3}`) divides `B(v)` for NO word
  `v` one move from `chr r A` (swaps and neighbour slides, wraps included). One-move deviations
  are supported at one point or constant on `[1, r)` (`one_move_shape`), so with
  `σ = A^{-1} mod r` the support of `κ` has `≤ 3` points.
* `lebel_conj_of_large_prime`, `lebel_strong_of_large_prime`: hence Lebel's Conjecture 11.1
  (some prime factor of `D` divides no radius-1 numerator) and its strong form (the largest prime
  factor works) hold for every primitive pair `(A, r)` such that `D` has a prime factor above the
  bound.

Prior art / credit: Lebel (`christoffel_collatz_v3.tex`, Conj. 11.1, radius 0, trinomial
reduction; computational check on 282 pairs), Mghirbi (Zenodo 21734655, the `t = 1` rotation
lift, Thm 6.3/6.4, Lemma 7.2), Solomon (Zenodo 22220730), Knight.

Scope: Conj. 11.1 is proved only CONDITIONALLY on `D` having a prime factor above
`≈ 16r·D^{2/3}` (heuristically ~40% of pairs; numerically ≥ 227/1018 pairs with `r < 90`).
For actual cycles the divisor form adds nothing, since for a cycle `q` itself divides `B`.
-/

namespace Collatz.NormLebel
open Collatz.NormGoal Collatz.NormReduce Collatz.NormShift Finset

/-- `Q ∣ q` and `Q ∣ B(v)` give `Q ∣ G a` for every rotation numerator. -/
theorem Q_dvd_G {Q r A : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hA : psum v r = A) (h3 : 3 ^ r ≤ 2 ^ A)
    (hQ : Q ∣ 2 ^ A - 3 ^ r) (hdvd : Q ∣ Bnum r v) (a : ℕ) : Q ∣ G r v a := by
  induction a with
  | zero => rwa [G_zero]
  | succ a ih =>
    have e := G_succ hr hA a
    have h4 : 3 ^ r * 2 ^ Pe r v a ≤ 2 ^ A * 2 ^ Pe r v a := Nat.mul_le_mul_right _ h3
    have : G r v (a + 1) = 3 * G r v a + (2 ^ A - 3 ^ r) * 2 ^ Pe r v a := by
      rw [Nat.sub_mul]; omega
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_of_dvd_left hQ _)

/-- **Core of the lift, divisor form.** `Q ∣ 2^A - 3^r`, `Q ∣ B(v)`, `a ≥ σ`, `κ_a ≠ 0`,
`κ_{a+j} = 0` for `T < j < r`, all exponents in `[0, E]`, and `(r 2^E)^r 2^{AT + r} < Q^r` give a
contradiction (copy of `NormShift.lift_core` with `q` replaced by `Q`). -/
theorem lift_core_dvd {Q r A σ m H E a T : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A) (hQ : Q ∣ 2 ^ A - 3 ^ r) (hdvd : Q ∣ Bnum r v)
    (ha : σ ≤ a) (hT : T < r)
    (hval1 : ∀ i, σ ≤ i → i * A / r ≤ H + Pe r v i)
    (hval2 : ∀ i, σ ≤ i → i * A / r ≤ H + m + Pe r v (i - σ))
    (hbd1 : ∀ i, σ ≤ i → H + Pe r v i - i * A / r ≤ E)
    (hbd2 : ∀ i, σ ≤ i → H + m + Pe r v (i - σ) - i * A / r ≤ E)
    (hka : Pe r v a ≠ m + Pe r v (a - σ))
    (hz : ∀ j, T < j → j < r → Pe r v (a + j) = m + Pe r v (a + j - σ))
    (hsz : (r * 2 ^ E) ^ r * 2 ^ (A * T + r) < Q ^ r) : False := by
  set q := 2 ^ A - 3 ^ r with hq_def
  have h3 : 3 ^ r ≤ 2 ^ A := by omega
  set c : ℕ → ℕ := fun i => i * A / r with hc_def
  set κ : ℕ → ℤ := fun j => (2 : ℤ) ^ (H + Pe r v (a + j) - c (a + j)) -
    2 ^ (H + m + Pe r v (a + j - σ) - c (a + j)) with hκ_def
  -- exact identity
  have hid : (2 : ℤ) ^ H * (G r v a : ℤ) - 2 ^ (H + m) * (G r v (a - σ) : ℤ) =
      ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * 2 ^ c (a + j) * κ j := by
    unfold G; push_cast
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro j _
    have hv1' := hval1 (a + j) (by omega)
    have hv2' := hval2 (a + j) (by omega)
    have e1 : (2 : ℤ) ^ c (a + j) * 2 ^ (H + Pe r v (a + j) - c (a + j)) =
        2 ^ H * 2 ^ Pe r v (a + j) := by
      rw [← pow_add, ← pow_add]; congr 1; simp only [hc_def]; omega
    have e2 : (2 : ℤ) ^ c (a + j) * 2 ^ (H + m + Pe r v (a + j - σ) - c (a + j)) =
        2 ^ (H + m) * 2 ^ Pe r v (a - σ + j) := by
      rw [← pow_add, ← pow_add, show a - σ + j = a + j - σ by omega]; congr 1
      simp only [hc_def]; omega
    simp only [hκ_def]
    linear_combination (-(3 : ℤ) ^ (r - 1 - j)) * e1 + (3 : ℤ) ^ (r - 1 - j) * e2
  -- window
  set N : ℤ := ∑ j ∈ range (T + 1), (3 : ℤ) ^ (T - j) * 2 ^ (c (a + j) - c a) * κ j with hN
  have hcmono : ∀ j, c a ≤ c (a + j) := by
    intro j; simp only [hc_def]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  have hwin : ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * 2 ^ c (a + j) * κ j =
      2 ^ c a * 3 ^ (r - 1 - T) * N := by
    rw [← sum_subset (range_subset_range.mpr (show T + 1 ≤ r by omega))]
    · rw [hN, mul_sum]; apply sum_congr rfl; intro j hj
      have := mem_range.mp hj
      have := hcmono j
      rw [show (3 : ℤ) ^ (r - 1 - j) = 3 ^ (r - 1 - T) * 3 ^ (T - j) by
          rw [← pow_add]; congr 1; omega,
        show (2 : ℤ) ^ c (a + j) = 2 ^ c a * 2 ^ (c (a + j) - c a) by
          rw [← pow_add]; congr 1; omega]
      ring
    · intro j hj hj'
      have h1 := mem_range.mp hj
      have h2 : T < j := by simp at hj'; omega
      have := hz j h2 h1
      have hk0 : κ j = 0 := by simp only [hκ_def]; rw [this, ← add_assoc, sub_self]
      rw [hk0, mul_zero]
  -- divisibility
  have hqG1 := Q_dvd_G hr hA h3 hQ hdvd a
  have hqG2 := Q_dvd_G hr hA h3 hQ hdvd (a - σ)
  have hqZ : (Q : ℤ) ∣ 2 ^ c a * 3 ^ (r - 1 - T) * N := by
    rw [← hwin, ← hid]
    exact dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hqG1) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hqG2) _)
  have hcop : IsCoprime (Q : ℤ) ((2 : ℤ) ^ c a * 3 ^ (r - 1 - T)) := by
    have : Nat.Coprime Q (2 ^ c a * 3 ^ (r - 1 - T)) := Nat.Coprime.coprime_dvd_left hQ <|
      Nat.Coprime.mul_right ((coprime_two hq).symm.pow_right _)
        ((coprime_three hr hq).symm.pow_right _)
    have h' := Nat.isCoprime_iff_coprime.mpr this
    push_cast at h'; exact h'
  have hqN : (Q : ℤ) ∣ N := by
    exact hcop.dvd_of_dvd_mul_left hqZ
  -- size
  set x : ℕ → ℕ := fun j => 3 ^ (T - j) * 2 ^ (c (a + j) - c a) with hx
  obtain ⟨jm, hjm, hmax⟩ := exists_max_image (range (T + 1)) x ⟨0, by simp⟩
  have hxr : r * 2 ^ E * x jm < Q := by
    have hp := term_pow_le (a := a) hr h3 (mem_range.mp hjm |> Nat.lt_succ_iff.mp)
    apply (Nat.pow_lt_pow_iff_left (show r ≠ 0 by omega)).mp
    calc (r * 2 ^ E * x jm) ^ r = (r * 2 ^ E) ^ r * (x jm) ^ r := by rw [mul_pow]
      _ ≤ (r * 2 ^ E) ^ r * 2 ^ (A * T + r) := Nat.mul_le_mul_left _ hp
      _ < Q ^ r := hsz
  have hκb : ∀ j, |κ j| ≤ 2 ^ E := by
    intro j
    exact abs_pow_sub_le (hbd1 (a + j) (by omega)) (hbd2 (a + j) (by omega))
  have hNle : |N| < Q := by
    calc |N| ≤ ∑ j ∈ range (T + 1), |(3 : ℤ) ^ (T - j) * 2 ^ (c (a + j) - c a) * κ j| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (T + 1), ((x jm : ℕ) : ℤ) * 2 ^ E := by
          apply sum_le_sum; intro j hj
          rw [abs_mul]
          have hxj : (3 : ℤ) ^ (T - j) * 2 ^ (c (a + j) - c a) = ((x j : ℕ) : ℤ) := by
            simp only [hx]; push_cast; ring
          rw [hxj, abs_of_nonneg (by positivity)]
          have : ((x j : ℕ) : ℤ) ≤ x jm := by exact_mod_cast hmax j hj
          exact mul_le_mul this (hκb j) (abs_nonneg _) (by positivity)
      _ = ((T + 1 : ℕ) : ℤ) * (x jm * 2 ^ E) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ((r * 2 ^ E * x jm : ℕ) : ℤ) := by
          push_cast
          have : ((T + 1 : ℕ) : ℤ) ≤ r := by exact_mod_cast (show T + 1 ≤ r by omega)
          nlinarith [show (0 : ℤ) ≤ x jm * 2 ^ E by positivity]
      _ < Q := by exact_mod_cast hxr
  have hN0 : N = 0 := Int.eq_zero_of_abs_lt_dvd hqN hNle
  -- 2-adic conclusion
  have heq : 2 ^ H * G r v a = 2 ^ (H + m) * G r v (a - σ) := by
    have : (2 : ℤ) ^ H * (G r v a : ℤ) - 2 ^ (H + m) * (G r v (a - σ) : ℤ) = 0 := by
      rw [hid, hwin, hN0, mul_zero]
    exact_mod_cast (sub_eq_zero.mp this)
  obtain ⟨u, hu, hGu⟩ := G_factor hr hv1 a
  obtain ⟨u', hu', hGu'⟩ := G_factor hr hv1 (a - σ)
  rw [hGu, hGu', ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add] at heq
  have := Collatz.NormShift.two_adic heq hu hu'
  omega

/-- **T1: shift lift for any divisor `Q` of `q`.** Let `3^r + 1 < 2^A`,
`Q ∣ 2^A - 3^r`, `v` with letters `≥ 1` below `r`, `psum v r = A`; a shift `σ < r` with
`σA = rm + t`, `1 ≤ t < r`; heights `1 - H ≤ ε ≤ E - H`; `g < r` with
`(r 2^E)^r 2^{A(r-1-g) + r} < Q^r`. If `κ` vanishes on some cyclic window `[x, x+g)`, then
`Q ∤ B(v)`. (`NormShift`'s `NormShift.shift_lift` is the case `Q = q`.) -/
theorem shift_lift_dvd {Q r A σ m t H E g : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A) (hQ : Q ∣ 2 ^ A - 3 ^ r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A) (hσr : σ < r) (hσ : σ * A = r * m + t)
    (ht : 1 ≤ t) (htr : t < r)
    (hlo : ∀ j < r, j * A / r + 1 ≤ H + psum v j) (hhi : ∀ j < r, H + psum v j ≤ j * A / r + E)
    (hg : g < r) (hsz : (r * 2 ^ E) ^ r * 2 ^ (A * (r - 1 - g) + r) < Q ^ r)
    (hrun : ∃ x < r, ∀ j < r, arc r x g j → quiet r A t σ v j) :
    ¬ Q ∣ Bnum r v := by
  intro hdvd
  have hr : 0 < r := by omega
  have hlo' : ∀ i, i * A / r + 1 ≤ H + Pe r v i := by
    intro i; have := hlo (i % r) (Nat.mod_lt _ hr); rw [Pe_mod hr hA, c_mod hr]; omega
  have hhi' : ∀ i, H + Pe r v i ≤ i * A / r + E := by
    intro i; have := hhi (i % r) (Nat.mod_lt _ hr); rw [Pe_mod hr hA, c_mod hr]; omega
  have hfl : ∀ i, σ ≤ i → i * A / r ≤ (i - σ) * A / r + m + 1 ∧
      (i - σ) * A / r + m ≤ i * A / r := by
    intro i hi; have := floor_shift hr hσ htr hi; split_ifs at this <;> omega
  have hZ := fun i (hi : σ ≤ i) => Z_iff (v := v) hr hA hσr hσ htr hi
  -- the support is nonempty
  have hne : ∃ ρ < r, ¬ quiet r A t σ v ρ := by
    by_contra hcon; push Not at hcon
    have hall : ∀ i, σ ≤ i → Pe r v i = m + Pe r v (i - σ) :=
      fun i hi => (hZ i hi).mpr (hcon _ (Nat.mod_lt _ hr))
    have hit : ∀ n, Pe r v (n * σ) = n * m := by
      intro n; induction n with
      | zero => simp [Pe_zero]
      | succ n ih =>
        have := hall ((n + 1) * σ) (Nat.le_mul_of_pos_left σ (by omega))
        rw [show (n + 1) * σ - σ = n * σ by rw [add_mul, one_mul, Nat.add_sub_cancel], ih] at this
        rw [this]; ring
    have h1 := hit r
    have h2 := Pe_add_mul hA 0 σ
    rw [zero_add, Pe_zero, zero_add] at h2
    rw [h1, mul_comm A σ, hσ] at h2; omega
  -- the free run, shifted by `r`
  obtain ⟨x, hx, hxrun⟩ := hrun
  have hrun' : ∀ k < g, Pe r v (x + r + k) = m + Pe r v (x + r + k - σ) := by
    intro k hk
    rw [hZ _ (by omega)]
    have hm : (x + r + k) % r = if r ≤ x + k then x + k - r else x + k := by
      rw [show x + r + k = (x + k) + r by ring, Nat.add_mod_right]; exact mod_lt_two (by omega)
    rw [hm]
    apply hxrun
    · split_ifs <;> omega
    · unfold arc; split_ifs <;> omega
  have hper : ∀ i, σ ≤ i → (Pe r v (i + r) = m + Pe r v (i + r - σ) ↔
      Pe r v i = m + Pe r v (i - σ)) := by
    intro i hi; rw [hZ _ (by omega), hZ _ hi, Nat.add_mod_right]
  -- first support point after the run
  have hex : ∃ j, ¬ (Pe r v (x + r + g + j) = m + Pe r v (x + r + g + j - σ)) := by
    obtain ⟨ρ, hρ, hρq⟩ := hne
    refine ⟨ρ + r * ((x + r + g) / r + 1) - (x + r + g), ?_⟩
    have hb := Nat.div_add_mod (x + r + g) r
    have hbl := Nat.mod_lt (x + r + g) hr
    have hge : x + r + g ≤ ρ + r * ((x + r + g) / r + 1) := by rw [mul_add, mul_one]; omega
    rw [Nat.add_sub_cancel' hge, hZ _ (by omega)]
    rwa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]
  classical
  have hj0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, Pe r v (x + r + g + j) = m + Pe r v (x + r + g + j - σ) :=
    fun j hj => by have := Nat.find_min hex hj; push Not at this; exact this
  apply lift_core_dvd (σ := σ) (m := m) (H := H) (E := E) (a := x + r + g + Nat.find hex)
    (T := r - 1 - g) hr hq hv1 hA hQ hdvd (by omega) (by omega)
  · intro i _; have := hlo' i; omega
  · intro i hi; have := hlo' (i - σ); have := hfl i hi; omega
  · intro i _; have := hhi' i; omega
  · intro i hi; have := hhi' (i - σ); have := hfl i hi; omega
  · exact hj0
  · intro j hj1 hj2
    have hσ' : σ ≤ x + r + g + Nat.find hex + j - r := by omega
    rw [show x + r + g + Nat.find hex + j = (x + r + g + Nat.find hex + j - r) + r by omega,
      hper _ hσ']
    by_cases hc : Nat.find hex + (j + g - r) < g
    · have := hrun' (Nat.find hex + (j + g - r)) hc
      rw [show x + r + g + Nat.find hex + j - r = x + r + (Nat.find hex + (j + g - r)) by omega]
      exact this
    · have := hmin (Nat.find hex + (j + g - r) - g) (by omega)
      rw [show x + r + g + Nat.find hex + j - r =
        x + r + g + (Nat.find hex + (j + g - r) - g) by omega]
      exact this
  · exact hsz


/-- **Free window from points.** A finite set `X` of points below `r` with `|X| g < r` leaves a
cyclic window `[x, x+g)` disjoint from `X`. -/
theorem free_points {r g : ℕ} (X : Finset ℕ) (hX : ∀ e ∈ X, e < r) (hg : g ≤ r)
    (hcount : X.card * g < r) : ∃ x < r, ∀ j < r, arc r x g j → j ∉ X := by
  classical
  rcases Nat.eq_zero_or_pos g with h0 | hg1
  · subst h0
    refine ⟨0, by omega, fun j hj h _ => ?_⟩
    unfold arc at h; omega
  by_contra hcon
  let bad := fun e => (range r).filter (fun x => ∃ j < r, arc r x g j ∧ arc r e 1 j)
  have hbad : ∀ e, e ≤ r → (bad e).card ≤ g := by
    intro e he
    have := card_meet (ℓ := 1) he (by omega) hg1 hg (bad e) (by
      intro x hx; simp only [bad, mem_filter, mem_range] at hx; exact hx)
    omega
  have hcover : range r ⊆ X.biUnion bad := by
    intro x hx
    by_contra hxn
    apply hcon
    refine ⟨x, mem_range.mp hx, fun j hj hxj h => hxn ?_⟩
    exact mem_biUnion.mpr ⟨j, h, mem_filter.mpr ⟨hx, j, hj, hxj, by unfold arc; omega⟩⟩
  have h1 := card_le_card hcover
  have h4 : (X.biUnion bad).card ≤ X.card * g := by
    calc _ ≤ ∑ e ∈ X, (bad e).card := card_biUnion_le
      _ ≤ ∑ e ∈ X, g := sum_le_sum (fun e he => hbad e (hX e he).le)
      _ = X.card * g := by rw [sum_const, smul_eq_mul]
  rw [card_range] at h1
  omega

/-! ### T2: one move, single divisor -/

theorem wt_zero_of_ne {r A ρ : ℕ} (hcop : Nat.Coprime A r) (hρ : ρ < r) (h0 : ρ ≠ 0) :
    NormShift.wt r A 1 ρ = 0 := by
  unfold NormShift.wt
  split_ifs with h
  · exact absurd (mod_inj hcop hρ (show 0 < r by omega) (by rw [show ρ * A % r = 0 by omega]; simp)) h0
  · rfl

theorem back_lt {r σ ρ : ℕ} (hσr : σ < r) (hρ : ρ < r) : back r σ ρ < r := by
  unfold back; split_ifs <;> omega

/-- Shape (P): deviation supported at one point `p`; then `κ` (for `t = 1`, `σA ≡ 1`) vanishes
off `{0, p, p + σ mod r}`. -/
theorem quiet_P {r A σ p ρ : ℕ} {v : ℕ → ℕ} (hcop : Nat.Coprime A r) (hσr : σ < r) (hp : p < r)
    (hρ : ρ < r) (heps : ∀ i < r, i ≠ p → eps r A v i = 0)
    (h0 : ρ ≠ 0) (h1 : ρ ≠ p) (h2 : ρ ≠ (p + σ) % r) : quiet r A 1 σ v ρ := by
  have hb := back_lt hσr hρ
  have hbp : back r σ ρ ≠ p := by
    intro h; apply h2; rw [mod_lt_two (by omega)]; unfold back at h; split_ifs at h ⊢ <;> omega
  unfold quiet
  rw [wt_zero_of_ne hcop hρ h0, heps ρ hρ h1, heps _ hb hbp]; simp

/-- Shape (W): deviation constant on `[1, r)`; then `κ` vanishes off `{0, σ}`. -/
theorem quiet_W {r A σ ρ : ℕ} {v : ℕ → ℕ} {c₀ : ℤ} (hcop : Nat.Coprime A r) (hσr : σ < r)
    (hρ : ρ < r) (heps : ∀ i, 1 ≤ i → i < r → eps r A v i = c₀)
    (h0 : ρ ≠ 0) (h1 : ρ ≠ σ) : quiet r A 1 σ v ρ := by
  have hb := back_lt hσr hρ
  have hb1 : 1 ≤ back r σ ρ := by unfold back; split_ifs <;> omega
  unfold quiet; rw [wt_zero_of_ne hcop hρ h0, heps ρ (by omega) hρ, heps _ hb1 hb]; simp

/-- **Deviation shapes of one-move words.** Every one-move neighbour `v` of `NormGoal.chr r A`
(`r ≥ 2`, `3^r + 1 < 2^A`) has letters `≥ 1`, `psum v r = A`, `|ε| ≤ 1`, and its deviation is
either supported at one point (P) or constant on `[1, r)` (W). -/
theorem one_move_shape {r A : ℕ} (hr : 2 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) {v : ℕ → ℕ}
    (hv : OneMove r (NormGoal.chr r A) v) :
    (∀ i < r, 1 ≤ v i) ∧ psum v r = A ∧ (∀ i < r, -1 ≤ eps r A v i ∧ eps r A v i ≤ 1) ∧
    ((∃ p < r, ∀ i < r, i ≠ p → eps r A v i = 0) ∨
     (∃ c₀ : ℤ, ∀ i, 1 ≤ i → i < r → eps r A v i = c₀)) := by
  have hr0 : 0 < r := by omega
  have hAr := r_lt_A hq
  have htwo : ∀ i, NormGoal.chr r A i = A / r ∨ NormGoal.chr r A i = A / r + 1 := fun i => by
    rw [chr_eq hr0]; split_ifs <;> simp
  rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, h2, k, hk, hkr, hkj, rfl⟩
  · have hps := fun i => psum_cswap (w := NormGoal.chr r A) hr hj i
    have hmr : (j + 1) % r < r := Nat.mod_lt _ hr0
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i _; unfold cswap; split_ifs <;> exact NormPlateau.chr_pos hr0 hAr.le _
    · have h := hps r
      simp only [hj, hmr, ite_true, psum_chr, Nat.mul_div_cancel_left _ hr0] at h
      omega
    · intro i _
      have h := hps i
      rw [psum_chr] at h
      have := htwo j; have := htwo ((j + 1) % r)
      unfold eps; split_ifs at h <;> omega
    · by_cases hjr : j + 1 < r
      · left
        refine ⟨j + 1, hjr, fun i _ hne => ?_⟩
        have h := hps i
        rw [psum_chr, Nat.mod_eq_of_lt hjr] at h
        unfold eps; split_ifs at h <;> omega
      · right
        have hm0 : (j + 1) % r = 0 := by rw [show j + 1 = r by omega, Nat.mod_self]
        refine ⟨(NormGoal.chr r A j : ℤ) - NormGoal.chr r A 0, fun i hi1 hir => ?_⟩
        have h := hps i
        rw [psum_chr, hm0] at h
        unfold eps; split_ifs at h <;> omega
  · obtain ⟨hv1, hsum, hps⟩ := NormPlateau.slide_facts hq hj hkr (Ne.symm hkj) h2
    refine ⟨hv1, hsum, ?_, ?_⟩
    · intro i _
      have h := hps i
      unfold eps; split_ifs at h <;> omega
    · rcases hk with hk | hk
      · by_cases hjr : j + 1 < r
        · rw [Nat.mod_eq_of_lt hjr] at hk
          left
          refine ⟨j + 1, hjr, fun i _ hne => ?_⟩
          have h := hps i
          unfold eps; split_ifs at h <;> omega
        · have hk0 : k = 0 := by rw [hk, show j + 1 = r by omega, Nat.mod_self]
          right
          refine ⟨1, fun i hi1 hir => ?_⟩
          have h := hps i
          unfold eps; split_ifs at h <;> omega
      · by_cases hkr' : k + 1 < r
        · rw [Nat.mod_eq_of_lt hkr'] at hk
          left
          refine ⟨j, hj, fun i _ hne => ?_⟩
          have h := hps i
          unfold eps; split_ifs at h <;> omega
        · have hj0 : j = 0 := by rw [← hk, show k + 1 = r by omega, Nat.mod_self]
          right
          refine ⟨-1, fun i hi1 hir => ?_⟩
          have h := hps i
          unfold eps; split_ifs at h <;> omega

/-- **T2: radius one is excluded by a single divisor above `≈ D^{2/3}`.**
For coprime `(A, r)`, `r ≥ 2`, `3^r + 1 < 2^A`, and ANY divisor `Q` of `D = 2^A - 3^r` with
`(8r)^r 2^{A(r - 1 - ⌊(r-1)/3⌋) + r} < Q^r` (i.e. `Q > 8r·2^{1 + A(r-1-⌊(r-1)/3⌋)/r}`),
no word `v` one move (cyclic adjacent swap, or slide to a cyclic neighbour) from the Christoffel
word `NormGoal.chr r A` has `Q ∣ B(v)`. Wrap moves included. Proof: shift lift with `σ = A^{-1} mod r`
(`t = 1`); the support of `κ` has at most 3 points, so a free window of length `⌊(r-1)/3⌋`. -/
theorem one_move_dvd (r A Q : ℕ) (hr : 2 ≤ r) (hcop : Nat.Coprime A r) (hq : 3 ^ r + 1 < 2 ^ A)
    (hQ : Q ∣ 2 ^ A - 3 ^ r)
    (hsz : (r * 2 ^ 3) ^ r * 2 ^ (A * (r - 1 - (r - 1) / 3) + r) < Q ^ r)
    (v : ℕ → ℕ) (hv : OneMove r (NormGoal.chr r A) v) : ¬ Q ∣ Bnum r v := by
  obtain ⟨hv1, hA, hbd, hsh⟩ := one_move_shape hr hq hv
  have hr0 : 0 < r := by omega
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hτ' : τ * A % r = 1 := by rw [mul_comm]; exact hτ
  have hσ : τ * A = r * (τ * A / r) + 1 := by
    have := Nat.div_add_mod (τ * A) r; rw [hτ'] at this; omega
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ'; simp at hτ'
  have hlo : ∀ j < r, j * A / r + 1 ≤ 2 + psum v j := fun j hj => by
    have := (hbd j hj).1; unfold eps at this; omega
  have hhi : ∀ j < r, 2 + psum v j ≤ j * A / r + 3 := fun j hj => by
    have := (hbd j hj).2; unfold eps at this; omega
  set g := (r - 1) / 3 with hg
  have hg3 : 3 * g ≤ r - 1 := by rw [hg]; omega
  apply shift_lift_dvd (σ := τ) (t := 1) (H := 2) (E := 3) (g := g) hq hQ hv1 hA hτr hσ le_rfl
    (by omega) hlo hhi (by omega) hsz
  rcases hsh with ⟨p, hp, hpe⟩ | ⟨c₀, hce⟩
  · obtain ⟨x, hx, hfree⟩ := free_points (r := r) (g := g) {0, p, (p + τ) % r}
      (by
        intro e he
        simp only [mem_insert, mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · omega
        · exact hp
        · exact Nat.mod_lt _ hr0)
      (by omega)
      (by have := Nat.mul_le_mul_right g (card_le_three (a := 0) (b := p) (c := (p + τ) % r))
          omega)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    have := hfree j hj hxj
    simp only [mem_insert, mem_singleton, not_or] at this
    exact quiet_P hcop hτr hp hj hpe this.1 this.2.1 this.2.2
  · obtain ⟨x, hx, hfree⟩ := free_points (r := r) (g := g) {0, τ}
      (by
        intro e he
        simp only [mem_insert, mem_singleton] at he
        rcases he with rfl | rfl
        · omega
        · exact hτr)
      (by omega)
      (by have := Nat.mul_le_mul_right g (card_le_two (a := 0) (b := τ))
          omega)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    have := hfree j hj hxj
    simp only [mem_insert, mem_singleton, not_or] at this
    exact quiet_W hcop hτr hj hce this.1 this.2

/-- **Lebel's Conjecture 11.1 above `D^{2/3}`.** For primitive `(A, r)`
(`gcd = 1`, `r ≥ 2`, `2^A > 3^r + 1`): if `D = 2^A - 3^r` has a prime factor `p` with
`(8r)^r 2^{A(r-1-⌊(r-1)/3⌋)+r} < p^r`, then some prime factor of `D` divides no radius-1
numerator, i.e. Lebel's single-prime conjecture holds for `(A, r)`. -/
theorem lebel_conj_of_large_prime (r A p : ℕ) (hr : 2 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hp : p.Prime) (hpD : p ∣ 2 ^ A - 3 ^ r)
    (hsz : (r * 2 ^ 3) ^ r * 2 ^ (A * (r - 1 - (r - 1) / 3) + r) < p ^ r) :
    ∃ p, p.Prime ∧ p ∣ 2 ^ A - 3 ^ r ∧
      ∀ v, OneMove r (NormGoal.chr r A) v → ¬ p ∣ Bnum r v :=
  ⟨p, hp, hpD, fun v hv => one_move_dvd r A p hr hcop hq hpD hsz v hv⟩

/-- **Lebel's strong form above `D^{2/3}`.** Under the hypotheses of
`lebel_conj_of_large_prime`, the LARGEST prime factor `P` of `D` divides no radius-1
numerator. -/
theorem lebel_strong_of_large_prime (r A p P : ℕ) (hr : 2 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hp : p.Prime) (hpD : p ∣ 2 ^ A - 3 ^ r)
    (hsz : (r * 2 ^ 3) ^ r * 2 ^ (A * (r - 1 - (r - 1) / 3) + r) < p ^ r)
    (hPD : P ∣ 2 ^ A - 3 ^ r) (hPmax : ∀ p', p'.Prime → p' ∣ 2 ^ A - 3 ^ r → p' ≤ P) :
    ∀ v, OneMove r (NormGoal.chr r A) v → ¬ P ∣ Bnum r v := by
  intro v hv
  have hle : p ^ r ≤ P ^ r := Nat.pow_le_pow_left (hPmax p hp hpD) r
  exact one_move_dvd r A P hr hcop hq hPD (lt_of_lt_of_le hsz hle) v hv

/-! ### T2': any gcd -/

/-! ### T3(b): rotation invariance -/

section Cycle
open CollatzProof

end Cycle


end Collatz.NormLebel

#print axioms Collatz.NormLebel.Q_dvd_G
#print axioms Collatz.NormLebel.lift_core_dvd
#print axioms Collatz.NormLebel.shift_lift_dvd
#print axioms Collatz.NormLebel.free_points
#print axioms Collatz.NormLebel.one_move_shape
#print axioms Collatz.NormLebel.one_move_dvd
#print axioms Collatz.NormLebel.lebel_conj_of_large_prime
#print axioms Collatz.NormLebel.lebel_strong_of_large_prime