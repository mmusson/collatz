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
  bound. `one_move_dvd_gcd` (T2'): any `d = gcd(A, r)` with `r/d ≥ 2`, window
  `⌊(r-1)/(d+2)⌋`. `lebel_witness_13_22`, `lebel_witness_10_21`: explicit instances (`D` prime).
* T3(a) `slide_word_coprime_dvd`, `no_cycle_slide_coprime_dvd`, `few_levels_coprime_dvd`:
  single-divisor versions of `NormShift`'s any-distance slide theorem (`g = ⌊r/10⌋`, `Q ≳ D^{0.9}`) and
  of T5.
* T3(b) `dvd_Bnum_rot`: for `Q ∣ q`, `Q ∣ B(rot_k v) ↔ Q ∣ B(v)`; `cycle_slide_rot_all`: no
  nontrivial `T`-cycle has a valuation word that is a rotation of a slide of `chr r L` (read from
  any start); `cycle_one_move_rot`: the `NormAll` bridge, start-free.

Prior art / credit: Lebel (`christoffel_collatz_v3.tex`, Conj. 11.1, radius 0, trinomial
reduction; computational check on 282 pairs), Mghirbi (Zenodo 21734655, the `t = 1` rotation
lift, Thm 6.3/6.4, Lemma 7.2), Solomon (Zenodo 22220730), Knight. New here (to our knowledge):
the divisor form of the lift and the resulting conditional proof of Conj. 11.1.

Honest scope: Conj. 11.1 is proved only CONDITIONALLY on `D` having a prime factor above
`≈ 16r·D^{2/3}` (heuristically ~40% of pairs; numerically ≥ 227/1018 pairs with `r < 90`).
Nothing new about actual cycles except start-freeness (`cycle_slide_rot_all`), since for a cycle
`q` itself divides `B`. NOT a milestone, NOT `no_nontrivial_cycles`.
-/

namespace CollatzSearch.NormLebel
open CollatzSearch.NormGoal CollatzSearch.NormReduce CollatzSearch.NormShift Finset

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
  have := CollatzSearch.NormShift.two_adic heq hu hu'
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

theorem quiet_P' {r A t σ p ρ : ℕ} {v : ℕ → ℕ} (hσr : σ < r) (hp : p < r)
    (hρ : ρ < r) (heps : ∀ i < r, i ≠ p → eps r A v i = 0) (hw : NormShift.wt r A t ρ = 0)
    (h1 : ρ ≠ p) (h2 : ρ ≠ (p + σ) % r) : quiet r A t σ v ρ := by
  have hb := back_lt hσr hρ
  have hbp : back r σ ρ ≠ p := by
    intro h; apply h2; rw [mod_lt_two (by omega)]; unfold back at h; split_ifs at h ⊢ <;> omega
  unfold quiet
  rw [hw, heps ρ hρ h1, heps _ hb hbp]; simp

theorem quiet_W' {r A t σ ρ : ℕ} {v : ℕ → ℕ} {c₀ : ℤ} (hσr : σ < r)
    (hρ : ρ < r) (heps : ∀ i, 1 ≤ i → i < r → eps r A v i = c₀) (hw : NormShift.wt r A t ρ = 0)
    (h0 : ρ ≠ 0) (h1 : ρ ≠ σ) : quiet r A t σ v ρ := by
  have hb := back_lt hσr hρ
  have hb1 : 1 ≤ back r σ ρ := by unfold back; split_ifs <;> omega
  unfold quiet; rw [hw, heps ρ (by omega) hρ, heps _ hb1 hb]; simp

/-- **T2': radius one, single divisor, any `gcd(A, r) = d` with `r/d ≥ 2`.**
Any divisor `Q` of `2^A - 3^r` with `(8r)^r 2^{A(r-1-⌊(r-1)/(d+2)⌋)+r} < Q^r` divides `B(v)`
for no one-move neighbour `v` of `chr r A`. (Shift `σ ≡ (A/d)^{-1} mod r/d`, `t = d` specials
`0, r/d, …`; the support of `κ` has at most `d + 2` points.) -/
theorem one_move_dvd_gcd (r A Q d : ℕ) (hr : 2 ≤ r) (hd : Nat.gcd A r = d) (hrd : 2 ≤ r / d)
    (hq : 3 ^ r + 1 < 2 ^ A) (hQ : Q ∣ 2 ^ A - 3 ^ r)
    (hsz : (r * 2 ^ 3) ^ r * 2 ^ (A * (r - 1 - (r - 1) / (d + 2)) + r) < Q ^ r)
    (v : ℕ → ℕ) (hv : OneMove r (NormGoal.chr r A) v) : ¬ Q ∣ Bnum r v := by
  obtain ⟨hv1, hA, hbd, hsh⟩ := one_move_shape hr hq hv
  have hr0 : 0 < r := by omega
  have hd0 : 0 < d := by rw [← hd]; exact Nat.gcd_pos_of_pos_right _ hr0
  set r' := r / d with hr'
  set A' := A / d with hA'
  have hrr : r = d * r' := by rw [hr', Nat.mul_div_cancel' (hd ▸ Nat.gcd_dvd_right A r)]
  have hAA : A = d * A' := by rw [hA', Nat.mul_div_cancel' (hd ▸ Nat.gcd_dvd_left A r)]
  have hcop : Nat.Coprime A' r' := by
    have := Nat.coprime_div_gcd_div_gcd (m := A) (n := r) (by rw [hd]; omega)
    rwa [hd] at this
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have e1 : A' * τ = r' * (A' * τ / r') + 1 := by
    have := Nat.div_add_mod (A' * τ) r'; rw [hτ] at this; omega
  set n := A' * τ / r' with hn
  have hrr' : r' ≤ r := by rw [hrr]; exact Nat.le_mul_of_pos_left _ hd0
  have hσr : τ < r := by omega
  have hσ : τ * A = r * n + d := by
    rw [hrr, hAA]
    have : d * (A' * τ) = d * (r' * n + 1) := by rw [e1]
    nlinarith [this]
  have hdr : d < r := by
    have : d * 2 ≤ d * r' := Nat.mul_le_mul_left _ hrd
    omega
  -- specials
  set E := (range d).image (fun i => i * r') with hE
  have hEr : ∀ e ∈ E, e < r := by
    intro e he; rw [hE, mem_image] at he; obtain ⟨i, hi, rfl⟩ := he
    have := mem_range.mp hi
    have : i * r' + r' ≤ d * r' := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ this
    omega
  have hspec : ∀ j < r, j * A % r < d → j ∈ E := by
    intro j hj hjd
    have h1 : j * A % r = d * (j * A' % r') := by
      rw [hrr, hAA, show j * (d * A') = d * (j * A') by ring, Nat.mul_mod_mul_left]
    have h2 : j * A' % r' = 0 := by
      by_contra hc
      have : d ≤ d * (j * A' % r') := Nat.le_mul_of_pos_right d (by omega)
      omega
    have h3 : r' ∣ j := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h2)
    obtain ⟨c, rfl⟩ := h3
    rw [hE, mem_image]
    refine ⟨c, mem_range.mpr ?_, by ring⟩
    by_contra hc
    have : d * r' ≤ r' * c := by rw [mul_comm r' c]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hEc : E.card ≤ d := by rw [hE]; exact card_image_le.trans (by simp)
  have hwt : ∀ j < r, j ∉ E → NormShift.wt r A d j = 0 := by
    intro j hj hjE; unfold NormShift.wt
    rw [ite_eq_right_iff]; intro h; exact absurd (hspec j hj h) hjE
  have h0E : (0 : ℕ) ∈ E := by rw [hE, mem_image]; exact ⟨0, mem_range.mpr hd0, by simp⟩
  have hlo : ∀ j < r, j * A / r + 1 ≤ 2 + psum v j := fun j hj => by
    have := (hbd j hj).1; unfold eps at this; omega
  have hhi : ∀ j < r, 2 + psum v j ≤ j * A / r + 3 := fun j hj => by
    have := (hbd j hj).2; unfold eps at this; omega
  set g := (r - 1) / (d + 2) with hg
  have hg3 : (d + 2) * g ≤ r - 1 := by rw [hg, mul_comm]; exact Nat.div_mul_le_self _ _
  have hgr : g < r := by
    have : 1 * g ≤ (d + 2) * g := Nat.mul_le_mul_right _ (by omega)
    omega
  apply shift_lift_dvd (σ := τ) (t := d) (H := 2) (E := 3) (g := g) hq hQ hv1 hA hσr hσ hd0
    hdr hlo hhi hgr hsz
  classical
  rcases hsh with ⟨p, hp, hpe⟩ | ⟨c₀, hce⟩
  · obtain ⟨x, hx, hfree⟩ := free_points (r := r) (g := g) (insert p (insert ((p + τ) % r) E))
      (by
        intro e he
        simp only [mem_insert] at he
        rcases he with rfl | rfl | he
        · exact hp
        · exact Nat.mod_lt _ hr0
        · exact hEr e he)
      (by omega)
      (by
        have h1 := card_insert_le p (insert ((p + τ) % r) E)
        have h2 := card_insert_le ((p + τ) % r) E
        have := Nat.mul_le_mul_right g (show (insert p (insert ((p + τ) % r) E)).card ≤ d + 2 by
          omega)
        omega)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    have := hfree j hj hxj
    simp only [mem_insert, not_or] at this
    exact quiet_P' hσr hp hj hpe (hwt j hj this.2.2) this.1 this.2.1
  · obtain ⟨x, hx, hfree⟩ := free_points (r := r) (g := g) (insert τ E)
      (by
        intro e he
        simp only [mem_insert] at he
        rcases he with rfl | he
        · exact hσr
        · exact hEr e he)
      (by omega)
      (by
        have h1 := card_insert_le τ E
        have := Nat.mul_le_mul_right g (show (insert τ E).card ≤ d + 2 by omega)
        omega)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    have := hfree j hj hxj
    simp only [mem_insert, not_or] at this
    exact quiet_W' hσr hj hce (hwt j hj this.2) (fun h => this.2 (h ▸ h0E)) this.1

/-! ### T3(b): rotation invariance -/

/-- Cyclic rotation of a word of length `r`: `(rot r k w) i = w ((i + k) mod r)`. -/
def rot (r k : ℕ) (w : ℕ → ℕ) (i : ℕ) : ℕ := w ((i + k) % r)

theorem Pe_rot {r k : ℕ} {v : ℕ → ℕ} (j : ℕ) : Pe r v (k + j) = Pe r v k + psum (rot r k v) j := by
  induction j with
  | zero => simp [psum]
  | succ j ih =>
    rw [← add_assoc, Pe_succ, ih]; unfold psum; rw [sum_range_succ]; simp only [rot]
    rw [add_comm j k]; ring

theorem G_rot {r k : ℕ} {v : ℕ → ℕ} : G r v k = 2 ^ Pe r v k * Bnum r (rot r k v) := by
  unfold G Bnum; rw [mul_sum]; apply sum_congr rfl; intro j _; rw [Pe_rot, pow_add]; ring

/-- For `Q ∣ q`: `Q ∣ G a ↔ Q ∣ B(v)` (the recursion `G (a+1) = 3 G a + q 2^{Pe a}` run both
ways, `gcd(Q, 3) = 1`). -/
theorem Q_dvd_G_iff {Q r A : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hq : 3 ^ r + 1 < 2 ^ A)
    (hQ : Q ∣ 2 ^ A - 3 ^ r) (hA : psum v r = A) (a : ℕ) : Q ∣ G r v a ↔ Q ∣ Bnum r v := by
  have hQ3 : Nat.Coprime Q 3 := ((coprime_three hr hq).symm).coprime_dvd_left hQ
  induction a with
  | zero => rw [G_zero]
  | succ a ih =>
    have e := G_succ hr hA a
    have h4 : 3 ^ r * 2 ^ Pe r v a ≤ 2 ^ A * 2 ^ Pe r v a := Nat.mul_le_mul_right _ (by omega)
    have : G r v (a + 1) = 3 * G r v a + (2 ^ A - 3 ^ r) * 2 ^ Pe r v a := by
      rw [Nat.sub_mul]; omega
    rw [this, Nat.dvd_add_left (dvd_mul_of_dvd_left hQ _), hQ3.dvd_mul_left]; exact ih

/-- **T3(b): rotation invariance.** For every divisor `Q` of `q = 2^A - 3^r`
(`3^r + 1 < 2^A`, `psum v r = A`) and every `k`: `Q ∣ B(rot_k v) ↔ Q ∣ B(v)`. -/
theorem dvd_Bnum_rot {Q r A k : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hq : 3 ^ r + 1 < 2 ^ A)
    (hQ : Q ∣ 2 ^ A - 3 ^ r) (hA : psum v r = A) :
    Q ∣ Bnum r (rot r k v) ↔ Q ∣ Bnum r v := by
  have hQ2 : Nat.Coprime Q 2 := ((coprime_two hq).symm).coprime_dvd_left hQ
  rw [← Q_dvd_G_iff hr hq hQ hA k, G_rot, (hQ2.pow_right _).dvd_mul_left]

section Cycle
open CollatzProof

/-- **T3(b) cycle form: start-free 2(c).** No nontrivial (`m ≠ 1`) positive
`T`-cycle with `r ≥ 2` odd steps and period `L` has a valuation word (read from ANY start) that
is a rotation of a slide of `chr r L` (one unit moved from `a`, `chr a ≥ 2`, to any `b ≠ a`). -/
theorem cycle_slide_rot_all {m L r k : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hm : m ≠ 1)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (a b : ℕ) (ha : a < r) (hb : b < r) (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r L a)
    (hv : ∀ i < r, v i = NormGoal.slide (NormGoal.chr r L) a b ((i + k) % r)) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨-, hr4⟩ := NormCycleAll.cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨-, hwsum, -⟩ := NormPlateau.slide_facts hq ha hb hab h2
  rw [NormPlateau.Bnum_congr (u := rot r k (NormGoal.slide (NormGoal.chr r L) a b)) hv,
    dvd_Bnum_rot (by omega) hq dvd_rfl hwsum] at hdiv
  exact NormShiftSlide.no_cycle_slide_allRA r L a b hr4 hq ha hb hab h2 hdiv

/-- **Start-free `NormAll` bridge.** A positive `T`-cycle with `r ≥ 2` odd steps and
period `L` whose valuation word, read from ANY start, is a rotation of `chr r L` or of a one-move
neighbour of it, is the trivial cycle: `L = 2r`, `v = (2,…,2)`, `m = 1`. -/
theorem cycle_one_move_rot {m L r k : ℕ} {v w : ℕ → ℕ} (hr : 2 ≤ r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hw : OneMove r (NormGoal.chr r L) w ∨ ∀ j < r, w j = NormGoal.chr r L j)
    (hv : ∀ i < r, v i = w ((i + k) % r)) :
    L = 2 * r ∧ (∀ j < r, v j = NormGoal.chr r L j) ∧ m = 1 := by
  have hr0 : 0 < r := by omega
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  have hwsum : psum w r = L := by
    rcases hw with h | h
    · exact (one_move_shape hr hq h).2.1
    · have : psum w r = psum (NormGoal.chr r L) r :=
        sum_congr rfl (fun i hi => h i (mem_range.mp hi))
      rw [this, psum_chr, Nat.mul_div_cancel_left _ hr0]
  rw [NormPlateau.Bnum_congr (u := rot r k w) hv, dvd_Bnum_rot hr0 hq dvd_rfl hwsum] at hdiv
  obtain ⟨h1, h2⟩ := (NormAll.one_move_classification r L hr hq w hw).mp hdiv
  have hc2 : ∀ j, NormGoal.chr r (2 * r) j = 2 := fun j => by
    unfold NormGoal.chr
    rw [show (j + 1) * (2 * r) = r * (2 * (j + 1)) by ring, show j * (2 * r) = r * (2 * j) by ring,
      Nat.mul_div_cancel_left _ hr0, Nat.mul_div_cancel_left _ hr0]; omega
  have hvc : ∀ j < r, v j = NormGoal.chr r L j := by
    intro j hj
    rw [hv j hj, h2 _ (Nat.mod_lt _ hr0), h1, hc2, hc2]
  exact NormBridge.cycle_one_move_christoffel hr hv1 hL hodd hcyc (Or.inr hvc)

end Cycle

/-! ### T3(a): divisor versions of the `NormShift` slide theorem and of T5 -/

/-- **T3(a) core: one unit slid any distance, single divisor, coprime.** As
`NormShift.slide_word_coprime`, with `q` replaced by any divisor `Q ∣ 2^A - 3^r` and the size
hypothesis `(8r)^r 2^{A(r-1-⌊r/10⌋)+r} < Q^r` stated directly. -/
theorem slide_word_coprime_dvd {Q r A a b : ℕ} {v : ℕ → ℕ} (hr : 3 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hQ : Q ∣ 2 ^ A - 3 ^ r) (ha : a < r) (hb : b < r) (hv1 : ∀ i < r, 1 ≤ v i)
    (hA : psum v r = A)
    (hps : ∀ j, psum v j + (if a < j then 1 else 0) = j * A / r + (if b < j then 1 else 0))
    (hg1 : 1 ≤ r / 10) (hsz : (r * 2 ^ 3) ^ r * 2 ^ (A * (r - 1 - r / 10) + r) < Q ^ r) :
    ¬ Q ∣ Bnum r v := by
  obtain ⟨heps, hlo, hhi⟩ := slide_bounds hps
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hτ' : τ * A % r = 1 := by rw [mul_comm]; exact hτ
  have hinj0 : ∀ j < r, j * A % r = 0 → j = 0 := fun j hj h =>
    mod_inj hcop hj (show 0 < r by omega) (by rw [h]; simp)
  have hinjτ : ∀ j < r, j * A % r = 1 → j = τ := fun j hj h =>
    mod_inj hcop hj hτr (by rw [h, hτ'])
  by_cases hcase : 20 * min τ (r - τ) ≤ 7 * r
  · -- `t = 1`, `σ = τ`
    have hσ : τ * A = r * (τ * A / r) + 1 := by
      have := Nat.div_add_mod (τ * A) r; rw [hτ'] at this; omega
    apply shift_lift_dvd (σ := τ) (t := 1) (H := 2) (E := 3) hq hQ hv1 hA hτr hσ le_rfl (by omega)
      (fun j _ => hlo j) (fun j _ => hhi j) (by omega) hsz
    apply slide_run {0} ha hb hτr (fun ρ _ => heps ρ) (by simp; omega)
      (fun j hj h => by simp only [mem_singleton]; exact hinj0 j hj (by omega)) hg1
    rw [card_singleton]; omega
  · -- `t = 2`, `σ = 2τ mod r`
    set σ := 2 * τ % r with hσdef
    have hσr : σ < r := Nat.mod_lt _ (by omega)
    have hσA : σ * A % r = 2 := by
      rw [hσdef, ← mod_mul_eq, mul_assoc, Nat.mul_mod, hτ', mul_one, Nat.mod_mod,
        Nat.mod_eq_of_lt (show 2 < r by omega)]
    have hσ : σ * A = r * (σ * A / r) + 2 := by
      have := Nat.div_add_mod (σ * A) r; rw [hσA] at this; omega
    have hσv : σ = if r ≤ 2 * τ then 2 * τ - r else 2 * τ := mod_lt_two (by omega)
    have hσ0 : σ ≠ 0 := by intro h0; rw [h0] at hσA; simp at hσA
    apply shift_lift_dvd (σ := σ) (t := 2) (H := 2) (E := 3) hq hQ hv1 hA hσr hσ (by omega) (by omega)
      (fun j _ => hlo j) (fun j _ => hhi j) (by omega) hsz
    apply slide_run {0, τ} ha hb hσr (fun ρ _ => heps ρ)
      (by intro e he; simp only [mem_insert, mem_singleton] at he; omega)
      (fun j hj h => by
        simp only [mem_insert, mem_singleton]
        rcases (show j * A % r = 0 ∨ j * A % r = 1 by omega) with h0 | h1
        · exact Or.inl (hinj0 j hj h0)
        · exact Or.inr (hinjτ j hj h1)) hg1
    have hc2 : ({0, τ} : Finset ℕ).card * (r / 10) ≤ 2 * (r / 10) :=
      Nat.mul_le_mul_right _ (card_le_two)
    have : 10 * min σ (r - σ) < 3 * r := by
      rw [hσv] at hσ0 ⊢; split_ifs at hσ0 ⊢ <;> omega
    omega

/-- **T5, single divisor.** As `NormShift.few_levels_coprime`, with `q` replaced by
any divisor `Q ∣ 2^A - 3^r`: coprime words with `|ε| ≤ H₀` and `J = |P|` cyclic level changes,
`g = ⌊r/(6J+3)⌋ ≥ 1` and `(r 2^{2H₀+1})^r 2^{A(r-1-g)+r} < Q^r`, have `Q ∤ B(v)`. -/
theorem few_levels_coprime_dvd {Q r A H₀ : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hQ : Q ∣ 2 ^ A - 3 ^ r) (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r A v c ≠ eps r A v (prv r c) → c ∈ P)
    (hup : ∀ j < r, psum v j ≤ j * A / r + H₀) (hdn : ∀ j < r, j * A / r ≤ psum v j + H₀)
    (hg1 : 1 ≤ r / (6 * P.card + 3))
    (hsz : (r * 2 ^ (2 * H₀ + 1)) ^ r * 2 ^ (A * (r - 1 - r / (6 * P.card + 3)) + r) < Q ^ r) :
    ¬ Q ∣ Bnum r v := by
  set J := P.card with hJ
  set g := r / (6 * J + 3) with hg
  have hgK : (6 * J + 3) * g ≤ r := by rw [hg, mul_comm]; exact Nat.div_mul_le_self _ _
  have hgr : g < r := by
    have : 3 * g ≤ (6 * J + 3) * g := Nat.mul_le_mul_right g (by omega)
    omega
  have hJr : 6 * J + 3 ≤ r := by
    have : (6 * J + 3) * 1 ≤ (6 * J + 3) * g := Nat.mul_le_mul_left _ hg1
    omega
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hτ' : τ * A % r = 1 := by rw [mul_comm]; exact hτ
  obtain ⟨t, ht1, htK, hdist⟩ := dirichlet (τ := τ) (K := 2 * J + 1) hr (by omega)
  set σ := t * τ % r with hσdef
  have hσr : σ < r := Nat.mod_lt _ hr
  have htr : t < r := by omega
  have hσA : σ * A % r = t := by
    rw [hσdef, ← mod_mul_eq, mul_assoc, Nat.mul_mod, hτ', mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt htr]
  have hσ : σ * A = r * (σ * A / r) + t := by
    have := Nat.div_add_mod (σ * A) r; rw [hσA] at this; omega
  -- specials
  set E := (range t).image (fun u => u * τ % r) with hE
  have hEr : ∀ e ∈ E, e < r := by
    intro e he; rw [hE, mem_image] at he; obtain ⟨u, _, rfl⟩ := he; exact Nat.mod_lt _ hr
  have hspec : ∀ j < r, j * A % r < t → j ∈ E := by
    intro j hj hjt
    rw [hE, mem_image]
    refine ⟨j * A % r, mem_range.mpr hjt, ?_⟩
    apply mod_inj hcop (Nat.mod_lt _ hr) hj
    rw [← mod_mul_eq, mul_assoc, Nat.mul_mod, hτ', mul_one, Nat.mod_mod, Nat.mod_mod]
  have hEc : E.card ≤ t := card_image_le.trans (by simp)
  -- heights
  have hlo : ∀ j < r, j * A / r + 1 ≤ (H₀ + 1) + psum v j := fun j hj => by
    have := hdn j hj; omega
  have hhi : ∀ j < r, (H₀ + 1) + psum v j ≤ j * A / r + (2 * H₀ + 1) := fun j hj => by
    have := hup j hj; omega
  apply shift_lift_dvd (σ := σ) (t := t) (H := H₀ + 1) (E := 2 * H₀ + 1) hq hQ hv1 hA hσr hσ ht1 htr
    hlo hhi (by omega) hsz
  -- counting
  have hcount : ∀ ℓ, (2 * J + 1) * ℓ < r → ∀ S : Finset ℕ, S.card ≤ J →
      S.card * (ℓ + g - 1) + E.card * g < r := by
    intro ℓ hℓ S hS
    have e1 : 3 * J * ((2 * J + 1) * ℓ + 1) ≤ 3 * J * r := Nat.mul_le_mul_left _ hℓ
    have e2 : (J + t) * ((6 * J + 3) * g) ≤ (J + t) * r := Nat.mul_le_mul_left _ hgK
    have e3 : (J + t) * r ≤ (3 * J + 1) * r := Nat.mul_le_mul_right _ (by omega)
    have key : (6 * J + 3) * (J * ℓ + J * g + t * g) < (6 * J + 3) * r := by nlinarith
    have key' : J * ℓ + J * g + t * g < r := Nat.lt_of_mul_lt_mul_left key
    have f1 : S.card * (ℓ + g - 1) ≤ J * (ℓ + g - 1) := Nat.mul_le_mul_right _ hS
    have f2 : E.card * g ≤ t * g := Nat.mul_le_mul_right _ hEc
    have f3 : J * (ℓ + g - 1) + J = J * ℓ + J * g := by
      rw [← mul_add_one, ← mul_add]; congr 1; omega
    omega
  have hback : ∀ ρ < r, back r σ ρ < r := by intro ρ hρ; unfold back; split_ifs <;> omega
  have hchg' : ∀ c < r, eps r A v c ≠ eps r A v (prv r c) → c ∈ P := hchg
  by_cases hs : σ ≤ r - σ
  · rw [min_eq_left hs] at hdist
    obtain ⟨x, hx, hfree⟩ := free_window2 (g := g) (ℓ := σ) P E (fun s hs => (hP s hs).le)
      (by omega) hEr hg1 (by omega) (hcount σ hdist P le_rfl)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2⟩ := hfree j hj hxj
    unfold quiet NormShift.wt
    rw [ite_eq_right_iff.mpr (fun h => absurd (hspec j hj h) n2), add_zero]
    exact cover_fwd (eps r A v) P hj hσr hchg' n1
  · rw [min_eq_right (by omega)] at hdist
    set S := P.image (fun c => red2 r (c + σ)) with hS
    obtain ⟨x, hx, hfree⟩ := free_window2 (g := g) (ℓ := r - σ) S E
      (by intro s hs; rw [hS, mem_image] at hs; obtain ⟨c, hc, rfl⟩ := hs
          have := hP c hc; unfold red2; split_ifs <;> omega)
      (by omega) hEr hg1 (by omega) (hcount (r - σ) hdist S card_image_le)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2⟩ := hfree j hj hxj
    unfold quiet NormShift.wt
    rw [ite_eq_right_iff.mpr (fun h => absurd (hspec j hj h) n2), add_zero]
    exact cover_bwd (eps r A v) P hj hσr hchg'
      (fun c hc => n1 _ (mem_image.mpr ⟨c, hc, rfl⟩))

/-- **T3(a): every slide of `chr`, single divisor.** For coprime `(A, r)`,
`r ≥ 10`, `3^r + 1 < 2^A`, and any divisor `Q` of `2^A - 3^r` with
`(8r)^r 2^{A(r-1-⌊r/10⌋)+r} < Q^r` (roughly `Q > D^{0.9}·16r`), no word obtained from `chr r A`
by moving one unit from `a` (`chr a ≥ 2`) to any other position `b` has `Q ∣ B`. -/
theorem no_cycle_slide_coprime_dvd (r A a b Q : ℕ) (hr : 10 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hQ : Q ∣ 2 ^ A - 3 ^ r) (ha : a < r) (hb : b < r) (hab : a ≠ b)
    (h2 : 2 ≤ NormGoal.chr r A a)
    (hsz : (r * 2 ^ 3) ^ r * 2 ^ (A * (r - 1 - r / 10) + r) < Q ^ r) :
    ¬ Q ∣ Bnum r (NormGoal.slide (NormGoal.chr r A) a b) := by
  obtain ⟨hv1, hsum, hps⟩ := NormPlateau.slide_facts hq ha hb hab h2
  exact slide_word_coprime_dvd (by omega) hcop hq hQ ha hb hv1 hsum hps (by omega) hsz

/-! ### Non-vacuity: Lebel's Conjecture 11.1 proved (not computed) for explicit pairs -/

/-- `(A, r) = (22, 13)`: `D = 2^22 - 3^13 = 2599981` is prime and meets the size bound, so
Lebel's single-prime conjecture holds for this primitive pair by `lebel_conj_of_large_prime`
(here `13 < 22 < 26`, inside Lebel's range `m < K < 2m`). -/
theorem lebel_witness_13_22 : ∃ p, p.Prime ∧ p ∣ 2 ^ 22 - 3 ^ 13 ∧
    ∀ v, OneMove 13 (NormGoal.chr 13 22) v → ¬ p ∣ Bnum 13 v := by
  apply lebel_conj_of_large_prime 13 22 2599981 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num

/-- `(A, r) = (21, 10)`: `D = 2^21 - 3^10 = 2038103` is prime and meets the size bound. -/
theorem lebel_witness_10_21 : ∃ p, p.Prime ∧ p ∣ 2 ^ 21 - 3 ^ 10 ∧
    ∀ v, OneMove 10 (NormGoal.chr 10 21) v → ¬ p ∣ Bnum 10 v := by
  apply lebel_conj_of_large_prime 10 21 2038103 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num

end CollatzSearch.NormLebel

#print axioms CollatzSearch.NormLebel.Q_dvd_G
#print axioms CollatzSearch.NormLebel.lift_core_dvd
#print axioms CollatzSearch.NormLebel.shift_lift_dvd
#print axioms CollatzSearch.NormLebel.free_points
#print axioms CollatzSearch.NormLebel.one_move_shape
#print axioms CollatzSearch.NormLebel.one_move_dvd
#print axioms CollatzSearch.NormLebel.lebel_conj_of_large_prime
#print axioms CollatzSearch.NormLebel.lebel_strong_of_large_prime
#print axioms CollatzSearch.NormLebel.one_move_dvd_gcd
#print axioms CollatzSearch.NormLebel.Pe_rot
#print axioms CollatzSearch.NormLebel.G_rot
#print axioms CollatzSearch.NormLebel.Q_dvd_G_iff
#print axioms CollatzSearch.NormLebel.dvd_Bnum_rot
#print axioms CollatzSearch.NormLebel.cycle_slide_rot_all
#print axioms CollatzSearch.NormLebel.cycle_one_move_rot
#print axioms CollatzSearch.NormLebel.slide_word_coprime_dvd
#print axioms CollatzSearch.NormLebel.few_levels_coprime_dvd
#print axioms CollatzSearch.NormLebel.no_cycle_slide_coprime_dvd
#print axioms CollatzSearch.NormLebel.lebel_witness_13_22
#print axioms CollatzSearch.NormLebel.lebel_witness_10_21
