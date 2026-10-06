import CollatzSearch.LcmBound

/-!
# Chebyshev-type bound `2^N · lcm(1..N) ≤ 2^37 · 7^N`
(classical, NOT new; NOT Goal progress — `no_nontrivial_cycles` remains OPEN)

Improves `LcmBound.Lc_le_four_pow` (`lcm(1..N) ≤ 4^N`) to `lcm(1..N) ≤ 2^37·3.5^N`.
* `floor_ineq`: `⌊3n/q⌋+⌊2n/q⌋+⌊n/q⌋ + [n<q≤6n] ≤ ⌊6n/q⌋`.
* `val_Mn`: Legendre ⇒ `v_p(C(6n,3n)C(3n,n)) ≥ #{i : n < p^i ≤ 6n}`.
* `Lc_six_dvd`: `lcm(1..6n) ∣ lcm(1..n)·C(6n,3n)C(3n,n)`; `Mn_le`: the multinomial is `≤ 432^n`.
* `Lc_le_cheb`: strong induction (base `N ≤ 192` from `4^N`; step via
  `2^{160+5j}·432^{33+j} ≤ 7^{160+5j}`).
-/

namespace CollatzSearch.LcmCheb

open CollatzSearch.LcmBound Nat

/-- Floor inequality (i): `3n/q + 2n/q + n/q ≤ 6n/q`, and (ii) with `+1` when `n < q ≤ 6n`. -/
theorem floor_ineq (n q : ℕ) (hq : 0 < q) :
    3*n/q + 2*n/q + n/q + (if n < q ∧ q ≤ 6*n then 1 else 0) ≤ 6*n/q := by
  set M := 6*n/q with hM
  have h2 : 3*n/q = M/2 := by
    rw [hM, Nat.div_div_eq_div_mul, show 6*n = 3*n*2 by ring,
      Nat.mul_div_mul_right _ _ (by norm_num : 0 < 2)]
  have h3 : 2*n/q = M/3 := by
    rw [hM, Nat.div_div_eq_div_mul, show 6*n = 2*n*3 by ring,
      Nat.mul_div_mul_right _ _ (by norm_num : 0 < 3)]
  have h6 : n/q = M/6 := by
    rw [hM, Nat.div_div_eq_div_mul, show 6*n = n*6 by ring,
      Nat.mul_div_mul_right _ _ (by norm_num : 0 < 6)]
  rw [h2, h3, h6]
  split_ifs with hc
  · have hM1 : 1 ≤ M := by
      rw [hM]; exact (Nat.le_div_iff_mul_le hq).mpr (by omega)
    have hM6 : M < 6 := by
      rw [hM]; exact (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    omega
  · omega

/-- The multinomial `C(6n,3n)·C(3n,n)`. -/
def Mn (n : ℕ) : ℕ := Nat.choose (6*n) (3*n) * Nat.choose (3*n) n

theorem Mn_ne_zero (n : ℕ) : Mn n ≠ 0 :=
  mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'

theorem Mn_mul (n : ℕ) : Mn n * ((3*n)! * (2*n)! * n !) = (6*n)! := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show 3*n ≤ 6*n by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3*n by omega)
  rw [show 6*n - 3*n = 3*n by omega] at h1
  rw [show 3*n - n = 2*n by omega] at h2
  unfold Mn
  calc Nat.choose (6*n) (3*n) * Nat.choose (3*n) n * ((3*n)! * (2*n)! * n !)
      = Nat.choose (6*n) (3*n) * (3*n)! * (Nat.choose (3*n) n * n ! * (2*n)!) := by ring
    _ = _ := by rw [h2, h1]

/-- Valuation bound: `v_p(Mn) ≥ #{i ∈ [1,B) : n < p^i ≤ 6n}`. -/
theorem val_Mn {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    ((Finset.Ico 1 (Nat.log p (6*n) + 1)).filter (fun i => n < p^i ∧ p^i ≤ 6*n)).card
      ≤ (Mn n).factorization p := by
  set B := Nat.log p (6*n) + 1 with hB
  have hfac := congrArg (fun x => x.factorization p) (Mn_mul n)
  rw [Nat.factorization_mul (Mn_ne_zero n) (by positivity), Finsupp.add_apply,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply] at hfac
  have hlt : ∀ k, k ≤ 6*n → Nat.log p k < B := fun k hk =>
    Nat.lt_succ_of_le (Nat.log_mono_right hk)
  rw [Nat.factorization_factorial hp (hlt (3*n) (by omega)),
    Nat.factorization_factorial hp (hlt (2*n) (by omega)),
    Nat.factorization_factorial hp (hlt n (by omega)),
    Nat.factorization_factorial hp (hlt (6*n) le_rfl)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 B, (3*n/p^i + 2*n/p^i + n/p^i
      + (if n < p^i ∧ p^i ≤ 6*n then 1 else 0)) ≤ ∑ i ∈ Finset.Ico 1 B, 6*n/p^i :=
    Finset.sum_le_sum fun i _ => floor_ineq n (p^i) (pow_pos hp.pos i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.card_filter] at hsum
  omega

/-- `lcm(1..6n) ∣ lcm(1..n) · Mn` for `n ≥ 1`. -/
theorem Lc_six_dvd {n : ℕ} (hn : 1 ≤ n) : Lc (6*n) ∣ Lc n * Mn n := by
  unfold Lc
  apply Finset.lcm_dvd
  intro j hj
  rw [Finset.mem_Icc] at hj
  simp only [id]
  have hX : Lc n * Mn n ≠ 0 := mul_ne_zero (Lc_ne_zero n) (Mn_ne_zero n)
  change j ∣ Lc n * Mn n
  rw [← Nat.factorization_prime_le_iff_dvd (by omega) hX]
  intro p hp
  set e := j.factorization p with he_def
  have hpe : p^e ∣ j := Nat.ordProj_dvd j p
  have hpej : p^e ≤ j := Nat.le_of_dvd (by omega) hpe
  have hp1 : 1 ≤ p^e := Nat.one_le_pow _ _ hp.pos
  rw [Nat.factorization_mul (Lc_ne_zero n) (Mn_ne_zero n), Finsupp.add_apply]
  by_cases hle : p^e ≤ n
  · have := (hp.pow_dvd_iff_le_factorization (Lc_ne_zero n)).mp (dvd_Lc hp1 hle)
    omega
  · push Not at hle
    set f := Nat.log p n with hf
    have hpf : p^f ≤ n := Nat.pow_log_le_self p (by omega)
    have hA : f ≤ (Lc n).factorization p :=
      (hp.pow_dvd_iff_le_factorization (Lc_ne_zero n)).mp
        (dvd_Lc (Nat.one_le_pow _ _ hp.pos) hpf)
    have hnf : n < p^(f+1) := Nat.lt_pow_succ_log_self hp.one_lt n
    have hfe : f < e := by
      by_contra hc
      push Not at hc
      have := Nat.pow_le_pow_right hp.pos hc
      omega
    have hel : e ≤ Nat.log p (6*n) := Nat.le_log_of_pow_le hp.one_lt (by omega)
    have hsub : Finset.Ioc f e ⊆
        (Finset.Ico 1 (Nat.log p (6*n) + 1)).filter (fun i => n < p^i ∧ p^i ≤ 6*n) := by
      intro i hi
      rw [Finset.mem_Ioc] at hi
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · exact lt_of_lt_of_le hnf (Nat.pow_le_pow_right hp.pos (by omega))
      · exact le_trans (Nat.pow_le_pow_right hp.pos hi.2) (by omega)
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at hcard
    have hB := val_Mn hp hn
    omega

/-- `Mn ≤ 432^n`. -/
theorem Mn_le (n : ℕ) : Mn n ≤ 432^n := by
  have h1 : Nat.choose (6*n) (3*n) ≤ 64^n := by
    calc _ ≤ 2^(6*n) := Nat.choose_le_two_pow _ _
      _ = 64^n := by rw [pow_mul]; norm_num
  have h2 : 4^n * Nat.choose (3*n) n ≤ 27^n := by
    have e := add_pow (2:ℕ) 1 (3*n)
    have hmem : 2*n ∈ Finset.range (3*n+1) := Finset.mem_range.mpr (by omega)
    have hs := Finset.single_le_sum (f := fun m => 2^m * 1^(3*n-m) * Nat.choose (3*n) m)
      (fun _ _ => Nat.zero_le _) hmem
    simp only [Nat.cast_id] at e
    rw [← e] at hs
    simp only [one_pow, mul_one] at hs
    have hsym : Nat.choose (3*n) (2*n) = Nat.choose (3*n) n := by
      rw [show 2*n = 3*n - n by omega]; exact Nat.choose_symm (by omega)
    rw [hsym] at hs
    calc 4^n * Nat.choose (3*n) n = 2^(2*n) * Nat.choose (3*n) n := by
          rw [pow_mul]; norm_num
      _ ≤ (2+1)^(3*n) := hs
      _ = 27^n := by rw [pow_mul]; norm_num
  have h4 : 4^n * Mn n ≤ 4^n * 432^n := by
    unfold Mn
    calc 4^n * (Nat.choose (6*n) (3*n) * Nat.choose (3*n) n)
        = Nat.choose (6*n) (3*n) * (4^n * Nat.choose (3*n) n) := by ring
      _ ≤ 64^n * 27^n := Nat.mul_le_mul h1 h2
      _ = 4^n * 432^n := by rw [← mul_pow, ← mul_pow]; norm_num
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

theorem Lc_mono {N M : ℕ} (h : N ≤ M) : Lc N ≤ Lc M := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Lc_ne_zero M))
  unfold Lc
  apply Finset.lcm_dvd
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact dvd_Lc hj.1 (le_trans hj.2 h)

/-- `lcm(1..6n) ≤ lcm(1..n)·432^n` for `n ≥ 1`. -/
theorem Lc_six_le {n : ℕ} (hn : 1 ≤ n) : Lc (6*n) ≤ Lc n * 432^n :=
  le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero (Lc_ne_zero n) (Mn_ne_zero n)))
    (Lc_six_dvd hn)) (Nat.mul_le_mul_left _ (Mn_le n))

theorem core_cheb (j : ℕ) : 2^(160+5*j) * 432^(33+j) ≤ 7^(160+5*j) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    calc 2^(160+5*(j+1)) * 432^(33+(j+1)) = (2^(160+5*j) * 432^(33+j)) * 13824 := by ring
      _ ≤ 7^(160+5*j) * 13824 := Nat.mul_le_mul_right _ ih
      _ ≤ 7^(160+5*j) * 16807 := Nat.mul_le_mul_left _ (by norm_num)
      _ = 7^(160+5*(j+1)) := by ring

theorem core_cheb' {n s : ℕ} (hn : 33 ≤ n) (hs : 5*n ≤ s + 5) : 2^s * 432^n ≤ 7^s := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 33 + j := ⟨n - 33, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = 160 + 5*j + s' := ⟨s - (160+5*j), by omega⟩
  calc 2^(160+5*j+s') * 432^(33+j) = 2^s' * (2^(160+5*j) * 432^(33+j)) := by ring
    _ ≤ 7^s' * 7^(160+5*j) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) _) (core_cheb j)
    _ = 7^(160+5*j+s') := by ring

theorem base_cheb {N : ℕ} (hN : N ≤ 192) : 8^N ≤ 2^37 * 7^N := by
  have h : 8^N * 7^(192-N) ≤ 2^37 * 7^N * 7^(192-N) := by
    calc 8^N * 7^(192-N) ≤ 8^N * 8^(192-N) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)
      _ = 8^192 := by rw [← pow_add]; congr 1; omega
      _ ≤ 2^37 * 7^192 := by norm_num
      _ = 2^37 * 7^N * 7^(192-N) := by rw [mul_assoc, ← pow_add]; congr 2; omega
  exact Nat.le_of_mul_le_mul_right h (by positivity)

/-- **Chebyshev-type bound (classical, not new):** `2^N · lcm(1..N) ≤ 2^37 · 7^N`,
i.e. `lcm(1..N) ≤ 2^37 · 3.5^N`. -/
theorem Lc_le_cheb (N : ℕ) : 2^N * Lc N ≤ 2^37 * 7^N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases le_or_gt N 192 with hN | hN
    · calc 2^N * Lc N ≤ 2^N * 4^N := Nat.mul_le_mul_left _ (Lc_le_four_pow N)
        _ = 8^N := by rw [← mul_pow]; norm_num
        _ ≤ _ := base_cheb hN
    · set n := (N+5)/6 with hn
      have hn1 : 33 ≤ n := by omega
      have hn6 : N ≤ 6*n := by omega
      have hn6' : 6*n ≤ N + 5 := by omega
      have hIH := ih n (by omega)
      have hLN : Lc N ≤ Lc n * 432^n := le_trans (Lc_mono hn6) (Lc_six_le (by omega))
      obtain ⟨s, hs⟩ : ∃ s, N = n + s := ⟨N - n, by omega⟩
      have hcore := core_cheb' (s := s) hn1 (by omega)
      have key : 2^n * (2^N * Lc N) ≤ 2^n * (2^37 * 7^N) := by
        calc 2^n * (2^N * Lc N) ≤ 2^n * (2^N * (Lc n * 432^n)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLN)
          _ = (2^n * Lc n) * (2^n * (2^s * 432^n)) := by rw [hs]; ring
          _ ≤ (2^37 * 7^n) * (2^n * 7^s) :=
              Nat.mul_le_mul hIH (Nat.mul_le_mul_left _ hcore)
          _ = 2^n * (2^37 * 7^N) := by rw [hs]; ring
      exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- Real form: `lcm(1..N) ≤ 2^37 (7/2)^N`. -/
theorem Lc_le_cheb_real (N : ℕ) : (Lc N : ℝ) ≤ 2^37 * (7/2)^N := by
  have h : ((2^N * Lc N : ℕ) : ℝ) ≤ ((2^37 * 7^N : ℕ) : ℝ) := by exact_mod_cast Lc_le_cheb N
  push_cast at h
  have h2 : (0:ℝ) < 2^N := by positivity
  rw [div_pow, mul_div_assoc']
  rw [le_div_iff₀ h2]; linarith

end CollatzSearch.LcmCheb

#print axioms CollatzSearch.LcmCheb.Lc_six_dvd
#print axioms CollatzSearch.LcmCheb.Mn_le
#print axioms CollatzSearch.LcmCheb.Lc_le_cheb
#print axioms CollatzSearch.LcmCheb.Lc_le_cheb_real
