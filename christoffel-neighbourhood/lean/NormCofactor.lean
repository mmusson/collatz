import NormAll
import NormTwo
import NormFlips

/-!
# Solomon's cofactor beyond one move (two sites, all sign patterns, `gcd(A,r) ≥ 2`)

Notation: `d = gcd(A, r) ≥ 2`, `r = d r'`, `A = d A'`, `U = 2^{A'}`, `V = 3^{r'}`,
`S_d = Sg U V d = Σ_{s<d} U^s V^{d-1-s}` (Solomon 2026, Zenodo 22220730, Prop. 6.3 — the
one-move case of the argument below is his; `NormAll.solomon_factor`: `S_d > 1`,
`gcd(S_d, 6) = 1`, `S_d ∣ 2^A - 3^r`, `S_d ∣ B(chr r A)`).

* `Sg_ge_two`: `U^{d-1} + V^{d-1} ≤ S_d`.
* `core_cofactor` (size lemma): if `S_d ∣ κ_a 3^γ + κ_b 2^δ` with `κ ∈ {2, -1}`, `1 ≤ γ`,
  `2γ ≤ r`, `δ r' < γ A' + r'`, then `d = 2`, `γ = r'`, `δ = A'`, `κ_a = κ_b`.
* `two_site_reduce`: a two-site `±1` partial-sum perturbation of `chr r A` with `q ∣ B(v)` forces
  `d = 2`, distance `r/2`, equal signs (difference `B(v) - B(chr)` is a two-monomial mod `S_d`,
  folded with `2^A ≡ 3^r`).
* `periodic_case`: that configuration (entries `≥ 1`) is a 2-fold repetition of a one-move
  neighbour of `chr r' A'`; `Bf_rep` + `NormAll` exclude it. (With zero entries allowed it is a
  genuine exception: `r = 6`, `A = 10`, sites 1, 4, both `-1`, block `(0,3,2)`, `5 ∣ 20`.)
* **T1** `no_cycle_two_site_noncoprime`, **T2** `no_cycle_two_right_flips_allRA` (`NormFlips`' two-right-flip
  theorem without coprimality), and cycle forms.

Corrects the `NormFlips` survey dead end "the two-move monomial difference can vanish mod `S_d`": it
vanishes only in the periodic `d = 2`, equal-sign, distance-`r/2` case, which reduces to `NormAll`.
Word-level results; not a milestone. Prior art: Knight, Lebel, Mghirbi, Solomon.
-/

namespace CollatzSearch.NormCofactor
open CollatzSearch.NormGoal CollatzSearch.NormReduce CollatzSearch.NormAll Finset

/-- `U^t ≤ Sg U V (t+1)`. -/
theorem pow_le_Sg (U V t : ℕ) : U ^ t ≤ Sg U V (t + 1) := by
  induction t with
  | zero => simp [Sg]
  | succ t ih =>
    show U ^ (t + 1) ≤ V ^ (t + 1) + U * Sg U V (t + 1)
    rw [pow_succ, mul_comm]
    have := Nat.mul_le_mul_left U ih
    omega

/-- (F2) `U^{d-1} + V^{d-1} ≤ Sg U V d` for `d ≥ 2`. -/
theorem Sg_ge_two (U V e : ℕ) : U ^ (e + 1) + V ^ (e + 1) ≤ Sg U V (e + 2) := by
  show U ^ (e + 1) + V ^ (e + 1) ≤ V ^ (e + 1) + U * Sg U V (e + 1)
  have := Nat.mul_le_mul_left U (pow_le_Sg U V e)
  rw [← pow_succ'] at this
  omega

/-- A nonzero multiple of `m` has absolute value at least `m`. -/
theorem not_dvd_of_abs_lt {m x : ℤ} (hx : x ≠ 0) (h : |x| < m) : ¬ m ∣ x :=
  fun hd => hx (Int.eq_zero_of_abs_lt_dvd hd h)

/-- `κ_a 3^γ + κ_b 2^δ ≠ 0` for `κ ∈ {2, -1}`, `γ ≥ 1` (it is not divisible by 3). -/
theorem kappa_ne_zero {κa κb : ℤ} (hb : κb = 2 ∨ κb = -1) {γ δ : ℕ} (hγ : 1 ≤ γ) :
    κa * 3 ^ γ + κb * 2 ^ δ ≠ 0 := by
  intro h
  have h3 : (3 : ℤ) ∣ κb * 2 ^ δ := by
    have : (3 : ℤ) ∣ κa * 3 ^ γ := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
    have h' : κb * 2 ^ δ = -(κa * 3 ^ γ) := by linarith
    rw [h']; exact this.neg_right
  rcases Int.prime_three.dvd_mul.mp h3 with h | h
  · rcases hb with rfl | rfl <;> norm_num at h
  · have := Int.prime_three.dvd_of_dvd_pow h; norm_num at this

/-- **Core size lemma.** Let `d ≥ 2`, `r' ≥ 1`, `3^{r'} < 2^{A'}`,
`S = Sg (2^{A'}) (3^{r'}) d`, `κ_a, κ_b ∈ {2, -1}`, `1 ≤ γ`, `2γ ≤ d r'`, `δ r' < γ A' + r'`.
If `S ∣ κ_a 3^γ + κ_b 2^δ` then `d = 2`, `γ = r'`, `δ = A'` and `κ_a = κ_b`. -/
theorem core_cofactor {d r' A' γ δ : ℕ} (hd : 2 ≤ d) (hr' : 0 < r') (hVU : 3 ^ r' < 2 ^ A')
    (hγ : 1 ≤ γ) (hγr : 2 * γ ≤ d * r') (hδ : δ * r' < γ * A' + r') {κa κb : ℤ}
    (ha : κa = 2 ∨ κa = -1) (hb : κb = 2 ∨ κb = -1)
    (hS : (Sg (2 ^ A') (3 ^ r') d : ℤ) ∣ κa * 3 ^ γ + κb * 2 ^ δ) :
    d = 2 ∧ γ = r' ∧ δ = A' ∧ κa = κb := by
  have hrA : r' < A' := by
    have : 2 ^ r' < 2 ^ A' := lt_of_le_of_lt
      (Nat.pow_le_pow_left (by norm_num) r') hVU
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hx0 := kappa_ne_zero (κa := κa) hb (δ := δ) hγ
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hSge := Sg_ge_two (2 ^ A') (3 ^ r') e
  -- generic small case
  have small : 3 ^ (γ + 1) ≤ (3 ^ r') ^ (e + 1) → 2 ^ (δ + 1) ≤ (2 ^ A') ^ (e + 1) → False := by
    intro h3 h2
    apply not_dvd_of_abs_lt hx0 _ hS
    have h3' : ((3 : ℤ) ^ (γ + 1)) ≤ ((3 ^ r' : ℕ) : ℤ) ^ (e + 1) := by exact_mod_cast h3
    have h2' : ((2 : ℤ) ^ (δ + 1)) ≤ ((2 ^ A' : ℕ) : ℤ) ^ (e + 1) := by exact_mod_cast h2
    have hS' : ((2 ^ A' : ℕ) : ℤ) ^ (e + 1) + ((3 ^ r' : ℕ) : ℤ) ^ (e + 1) ≤
        (Sg (2 ^ A') (3 ^ r') (e + 2) : ℤ) := by exact_mod_cast hSge
    have p3 : (0 : ℤ) < 3 ^ γ := by positivity
    have p2 : (0 : ℤ) < 2 ^ δ := by positivity
    rw [pow_succ] at h3' h2'
    rw [abs_lt]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> constructor <;> nlinarith
  have hδ' : ∀ m : ℕ, γ + 1 ≤ m * r' → δ + 1 ≤ m * A' := by
    intro m hm
    by_contra hc
    have h1 : m * A' * r' ≤ δ * r' := Nat.mul_le_mul_right _ (by omega)
    have h2 : (γ + 1) * A' ≤ m * r' * A' := Nat.mul_le_mul_right _ hm
    have h3 : r' * A' = A' * r' := mul_comm _ _
    nlinarith
  have pw3 : ∀ m : ℕ, γ + 1 ≤ m * r' → 3 ^ (γ + 1) ≤ (3 ^ r') ^ m := by
    intro m hm; rw [← pow_mul, mul_comm r' m]; exact Nat.pow_le_pow_right (by norm_num) hm
  have pw2 : ∀ m : ℕ, γ + 1 ≤ m * r' → 2 ^ (δ + 1) ≤ (2 ^ A') ^ m := by
    intro m hm; rw [← pow_mul, mul_comm A' m]; exact Nat.pow_le_pow_right (by norm_num) (hδ' m hm)
  rcases Nat.lt_or_ge 0 e with he | he
  · -- d ≥ 3
    exfalso
    have : γ + 1 ≤ (e + 1) * r' := by
      rcases Nat.lt_or_ge r' 2 with h1 | h1
      · have : r' = 1 := by omega
        subst this; omega
      · nlinarith
    exact small (pw3 _ this) (pw2 _ this)
  · have he0 : e = 0 := by omega
    subst he0
    simp only [zero_add] at *
    rcases Nat.lt_or_ge γ r' with hγ1 | hγ1
    · exfalso
      exact small (by simpa using pw3 1 (by omega)) (by simpa using pw2 1 (by omega))
    · have hγe : γ = r' := by omega
      subst hγe
      -- δ ≤ A'
      have hδA : δ ≤ A' := by
        by_contra hc
        have : (A' + 1) * γ ≤ δ * γ := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      have hS2 : (Sg (2 ^ A') (3 ^ γ) 2 : ℤ) = 3 ^ γ + 2 ^ A' := by
        simp [Sg]
      rw [hS2] at hS
      have hV : (3 : ℤ) ^ γ < 2 ^ A' := by exact_mod_cast hVU
      have hpd : (2 : ℤ) ^ δ ≤ 2 ^ A' := pow_le_pow_right₀ (by norm_num) hδA
      have p3 : (0 : ℤ) < 3 ^ γ := by positivity
      have p2 : (0 : ℤ) < 2 ^ δ := by positivity
      -- the equal-sign subcase forces 2^δ = 2^A'
      have eqcase : (3 : ℤ) ^ γ + 2 ^ δ ≠ 3 ^ γ + 2 ^ A' →
          ¬ ((3 : ℤ) ^ γ + 2 ^ A') ∣ 3 ^ γ + 2 ^ δ := by
        intro hne hd
        obtain ⟨m, hm⟩ := hd
        have hm1 : m = 1 := by
          have : 0 < m := by nlinarith
          have : m < 2 := by nlinarith
          omega
        rw [hm1, mul_one] at hm; exact hne hm
      have hodd : IsCoprime ((3 : ℤ) ^ γ + 2 ^ A') 2 := by
        have hA'1 : 1 ≤ A' := by omega
        rw [show (2 : ℤ) ^ A' = 2 * 2 ^ (A' - 1) by rw [← pow_succ']; congr 1; omega]
        have : IsCoprime ((3 : ℤ) ^ γ) 2 := by
          apply IsCoprime.pow_left; rw [Int.isCoprime_iff_gcd_eq_one]; rfl
        exact (IsCoprime.add_mul_left_left this _)
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · refine ⟨by simp, rfl, ?_, rfl⟩
        have hd' : ((3 : ℤ) ^ γ + 2 ^ A') ∣ 2 * (3 ^ γ + 2 ^ δ) := by
          rw [show 2 * ((3 : ℤ) ^ γ + 2 ^ δ) = 2 * 3 ^ γ + 2 * 2 ^ δ by ring]; exact hS
        have := hodd.dvd_of_dvd_mul_left hd'
        by_contra hc
        refine eqcase ?_ this
        intro h
        have : (2 : ℤ) ^ δ = 2 ^ A' := by linarith
        exact hc (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this))
      · exfalso
        apply not_dvd_of_abs_lt hx0 _ hS
        rw [abs_lt]; constructor <;> nlinarith
      · exfalso
        obtain ⟨m, hm⟩ := hS
        have hm0 : 0 ≤ m := by nlinarith
        have hm1 : m < 2 := by nlinarith
        rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
        · exact hx0 (by linarith)
        · rcases Nat.lt_or_ge δ A' with hδ1 | hδ1
          · have : (2 : ℤ) ^ (δ + 1) ≤ 2 ^ A' := pow_le_pow_right₀ (by norm_num) hδ1
            rw [pow_succ] at this; nlinarith
          · have hδe : δ = A' := by omega
            subst hδe
            have h2 : (2 : ℤ) ^ δ = 2 * 3 ^ γ := by linarith
            have : (3 : ℤ) ∣ 2 ^ δ := by rw [h2]; exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
            have := Int.prime_three.dvd_of_dvd_pow this; norm_num at this
      · refine ⟨by simp, rfl, ?_, rfl⟩
        have hd' : ((3 : ℤ) ^ γ + 2 ^ A') ∣ 3 ^ γ + 2 ^ δ := by
          have := hS.neg_right; rw [show -(-1 * (3 : ℤ) ^ γ + -1 * 2 ^ δ) = 3 ^ γ + 2 ^ δ by ring] at this
          exact this
        by_contra hc
        refine eqcase ?_ hd'
        intro h
        have : (2 : ℤ) ^ δ = 2 ^ A' := by linarith
        exact hc (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this))


/-- `κ(ε) = 2` for `ε = 1` and `-1` otherwise: `2(2^{c+ε} - 2^c) = κ(ε) 2^c`. -/
def kap (ε : ℤ) : ℤ := if ε = 1 then 2 else -1

theorem kap_cases (ε : ℤ) : kap ε = 2 ∨ kap ε = -1 := by
  unfold kap; split_ifs <;> simp

theorem kap_inj {ε₁ ε₂ : ℤ} (h1 : ε₁ = 1 ∨ ε₁ = -1) (h2 : ε₂ = 1 ∨ ε₂ = -1)
    (h : kap ε₁ = kap ε₂) : ε₁ = ε₂ := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all [kap]

theorem two_mul_diff {R : Type*} [CommRing R] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {a c : ℕ}
    (h : (a : ℤ) = c + ε) : (2 : R) * (2 ^ a - 2 ^ c) = (kap ε : R) * 2 ^ c := by
  rcases hε with rfl | rfl
  · have : a = c + 1 := by omega
    subst this; simp [kap, pow_succ]; ring
  · have : c = a + 1 := by omega
    subst this; simp [kap, pow_succ]; ring

/-- (F1) `3^{r'} < 2^{A'}` from `3^{d r'} + 1 < 2^{d A'}`. -/
theorem block_lt {d r' A' : ℕ} (hd : 0 < d) (hq : 3 ^ (d * r') + 1 < 2 ^ (d * A')) :
    3 ^ r' < 2 ^ A' := by
  by_contra h
  have := Nat.pow_le_pow_left (not_lt.mp h) d
  rw [← pow_mul, ← pow_mul, mul_comm A' d, mul_comm r' d] at this
  omega

/-- Floor bounds (F3) for `c_j = ⌊jA/r⌋`. -/
theorem floor_bounds {r A k₁ k₂ : ℕ} (hr : 0 < r) (h12 : k₁ ≤ k₂) :
    k₁ * A / r ≤ k₂ * A / r ∧
    (k₂ * A / r - k₁ * A / r) * r < (k₂ - k₁) * A + r ∧
    (k₂ - k₁) * A < (k₂ * A / r - k₁ * A / r) * r + r := by
  have hle : k₁ * A / r ≤ k₂ * A / r := Nat.div_le_div_right (Nat.mul_le_mul_right _ h12)
  refine ⟨hle, ?_, ?_⟩
  · have a1 := Nat.div_mul_le_self (k₂ * A) r
    have a2 := Nat.lt_div_mul_add (a := k₁ * A) hr
    have a3 : k₁ * A ≤ k₂ * A := Nat.mul_le_mul_right _ h12
    rw [Nat.sub_mul, Nat.sub_mul]
    have a4 := Nat.mul_le_mul_right r hle
    generalize k₂ * A / r * r = P at *
    generalize k₁ * A / r * r = Q at *
    generalize k₂ * A = K2 at *
    generalize k₁ * A = K1 at *
    omega
  · have a1 := Nat.div_mul_le_self (k₁ * A) r
    have a2 := Nat.lt_div_mul_add (a := k₂ * A) hr
    have a3 : k₁ * A ≤ k₂ * A := Nat.mul_le_mul_right _ h12
    rw [Nat.sub_mul, Nat.sub_mul]
    have a4 := Nat.mul_le_mul_right r hle
    generalize k₂ * A / r * r = P at *
    generalize k₁ * A / r * r = Q at *
    generalize k₂ * A = K2 at *
    generalize k₁ * A = K1 at *
    omega

/-- **Two-site reduction.** In repetition coordinates `r = d r'`, `A = d A'`
(`d ≥ 2`), if `q ∣ B(v)` where the partial sums of `v` are those of `chr r A` plus
`ε₁, ε₂ ∈ {±1}` at `0 < k₁ < k₂ < r`, then `d = 2`, `k₂ = k₁ + r'` and `ε₁ = ε₂`. -/
theorem two_site_reduce {d r' A' r A : ℕ} (hrd : r = d * r') (hAd : A = d * A') (hd : 2 ≤ d)
    (hr' : 0 < r') (hq : 3 ^ r + 1 < 2 ^ A)
    {k₁ k₂ : ℕ} (h1 : 0 < k₁) (h12 : k₁ < k₂) (h2 : k₂ < r) {ε₁ ε₂ : ℤ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    {v : ℕ → ℕ}
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i + (if i = k₁ then ε₁ else 0) +
      (if i = k₂ then ε₂ else 0))
    (hdiv : (2 ^ A - 3 ^ r) ∣ Bnum r v) : d = 2 ∧ k₂ = k₁ + r' ∧ ε₁ = ε₂ := by
  subst hrd hAd
  set S := Sg (2 ^ A') (3 ^ r') d with hSdef
  obtain ⟨hS1, hS2, hS3, hSq, hSB⟩ := solomon_factor hd hr' hq
  rw [← hSdef] at hS1 hS2 hS3 hSq hSB
  have hVU := block_lt (by omega) hq
  have hr0 : 0 < d * r' := by positivity
  have hnt : Nontrivial (ZMod S) := ZMod.nontrivial_iff.mpr (by omega)
  have h2u : IsUnit (2 : ZMod S) := by simpa using (ZMod.unitOfCoprime 2 hS2).isUnit
  have h3u : IsUnit (3 : ZMod S) := by simpa using (ZMod.unitOfCoprime 3 hS3).isUnit
  have hBv : (Bnum (d * r') v : ZMod S) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_trans hSq hdiv)
  have hBw : (Bnum (d * r') (NormGoal.chr (d * r') (d * A')) : ZMod S) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hSB
  have hH : (2 : ZMod S) ^ (d * A') = 3 ^ (d * r') := by
    have : ((2 ^ (d * A') - 3 ^ (d * r') : ℕ) : ZMod S) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hSq
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    exact sub_eq_zero.mp this
  rw [cast_Bnum] at hBv hBw
  set c₁ := k₁ * (d * A') / (d * r') with hc₁
  set c₂ := k₂ * (d * A') / (d * r') with hc₂
  have hv1 := hv k₁ (by omega)
  have hv2 := hv k₂ h2
  rw [if_pos rfl, if_neg (by omega), psum_chr] at hv1
  rw [if_neg (by omega), if_pos rfl, psum_chr] at hv2
  rw [add_zero] at hv1
  rw [add_zero] at hv2
  rw [← hc₁] at hv1
  rw [← hc₂] at hv2
  set a₁ := psum v k₁
  set a₂ := psum v k₂
  -- the difference has two terms
  have hdiff : ∑ i ∈ range (d * r'), ((3 : ZMod S) ^ (d * r' - 1 - i) * 2 ^ psum v i -
      3 ^ (d * r' - 1 - i) * 2 ^ psum (NormGoal.chr (d * r') (d * A')) i) =
      (3 ^ (d * r' - 1 - k₁) * 2 ^ a₁ - 3 ^ (d * r' - 1 - k₁) * 2 ^ c₁) +
      (3 ^ (d * r' - 1 - k₂) * 2 ^ a₂ - 3 ^ (d * r' - 1 - k₂) * 2 ^ c₂) := by
    rw [sum_eq_add_of_mem k₁ k₂ (mem_range.mpr (by omega)) (mem_range.mpr h2) (by omega)]
    · simp only [psum_chr, a₁, a₂, c₁, c₂]
    · intro i hi hne
      have hvi := hv i (mem_range.mp hi)
      rw [if_neg hne.1, if_neg hne.2] at hvi
      have : psum v i = psum (NormGoal.chr (d * r') (d * A')) i := by omega
      rw [this, sub_self]
  rw [sum_sub_distrib, hBv, hBw, sub_zero] at hdiff
  -- multiply by 2
  have e1 := two_mul_diff (R := ZMod S) hε₁ hv1
  have e2 := two_mul_diff (R := ZMod S) hε₂ hv2
  have hcle := floor_bounds (r := d * r') (A := d * A') hr0 h12.le
  rw [← hc₁, ← hc₂] at hcle
  obtain ⟨hc12, hF1, hF2⟩ := hcle
  set β := k₂ - k₁ with hβ
  set α := c₂ - c₁ with hα
  have p3 : (3 : ZMod S) ^ (d * r' - 1 - k₁) = 3 ^ (d * r' - 1 - k₂) * 3 ^ β := by
    rw [← pow_add]; congr 1; omega
  have p2 : (2 : ZMod S) ^ c₂ = 2 ^ c₁ * 2 ^ α := by
    rw [← pow_add]; congr 1; omega
  have hstar0 : (3 : ZMod S) ^ (d * r' - 1 - k₂) * 2 ^ c₁ *
      ((kap ε₁ : ZMod S) * 3 ^ β + (kap ε₂ : ZMod S) * 2 ^ α) = 0 := by
    linear_combination (-2 : ZMod S) * hdiff - 3 ^ (d * r' - 1 - k₁) * e1 -
      3 ^ (d * r' - 1 - k₂) * e2 - (kap ε₁ : ZMod S) * 2 ^ c₁ * p3 - (kap ε₂ : ZMod S) * 3 ^ (d * r' - 1 - k₂) * p2
  have hstar : (kap ε₁ : ZMod S) * 3 ^ β + (kap ε₂ : ZMod S) * 2 ^ α = 0 :=
    ((h3u.pow _).mul (h2u.pow _)).mul_right_eq_zero.mp hstar0
  clear_value a₁ a₂ α β c₁ c₂
  have hβ1 : 1 ≤ β := by omega
  rcases le_or_gt (2 * β) (d * r') with hb | hb
  · have hz : ((kap ε₁ * 3 ^ β + kap ε₂ * 2 ^ α : ℤ) : ZMod S) = 0 := by push_cast; exact hstar
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ S).mp hz
    have hδ : α * r' < β * A' + r' := by
      apply Nat.lt_of_mul_lt_mul_left (a := d)
      calc d * (α * r') = α * (d * r') := by ring
        _ < β * (d * A') + d * r' := hF1
        _ = d * (β * A' + r') := by ring
    obtain ⟨hd2, hβr, -, hk⟩ :=
      core_cofactor hd hr' hVU hβ1 hb hδ (kap_cases ε₁) (kap_cases ε₂) hdvd
    exact ⟨hd2, by omega, kap_inj hε₁ hε₂ hk⟩
  · have hc2A : c₂ ≤ d * A' := by
      rw [hc₂]; refine Nat.div_le_of_le_mul ?_
      exact Nat.mul_le_mul_right (d * A') (show k₂ ≤ d * r' by omega)
    set γ := d * r' - β with hγ
    set δ := d * A' - α with hδdef
    clear_value γ δ
    have q3 : (3 : ZMod S) ^ β * 3 ^ γ = 3 ^ (d * r') := by rw [← pow_add]; congr 1; omega
    have q2 : (2 : ZMod S) ^ δ * 2 ^ α = 2 ^ (d * A') := by rw [← pow_add]; congr 1; omega
    have hfold0 : (3 : ZMod S) ^ β * ((kap ε₂ : ZMod S) * 3 ^ γ + (kap ε₁ : ZMod S) * 2 ^ δ) = 0 := by
      linear_combination (2 : ZMod S) ^ δ * hstar + (kap ε₂ : ZMod S) * q3 -
        (kap ε₂ : ZMod S) * q2 - (kap ε₂ : ZMod S) * hH
    have hfold := (h3u.pow β).mul_right_eq_zero.mp hfold0
    have hz : ((kap ε₂ * 3 ^ γ + kap ε₁ * 2 ^ δ : ℤ) : ZMod S) = 0 := by push_cast; exact hfold
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ S).mp hz
    have hδ : δ * r' < γ * A' + r' := by
      apply Nat.lt_of_mul_lt_mul_left (a := d)
      have e1 : d * (δ * r') = δ * (d * r') := by ring
      have e2 : d * (γ * A' + r') = γ * (d * A') + d * r' := by ring
      rw [e1, e2, hγ, hδdef, Nat.sub_mul, Nat.sub_mul]
      have f1 : α * (d * r') ≤ d * A' * (d * r') := Nat.mul_le_mul_right _ (by omega)
      have f2 : β * (d * A') ≤ d * r' * (d * A') := Nat.mul_le_mul_right _ (by omega)
      have f3 : d * r' * (d * A') = d * A' * (d * r') := mul_comm _ _
      generalize α * (d * r') = X at *
      generalize β * (d * A') = Y at *
      generalize d * r' * (d * A') = M at *
      omega
    obtain ⟨hd2, hγr, -, hk⟩ :=
      core_cofactor hd hr' hVU (by omega) (by omega) hδ (kap_cases ε₂) (kap_cases ε₁) hdvd
    subst hd2
    exact ⟨rfl, by omega, (kap_inj hε₂ hε₁ hk).symm⟩

theorem psum_chr_two {r' A' : ℕ} (j : ℕ) :
    psum (NormGoal.chr (2 * r') (2 * A')) j = j * A' / r' := by
  rw [psum_chr, show j * (2 * A') = 2 * (j * A') by ring]
  exact Nat.mul_div_mul_left _ _ (by norm_num)

/-- **The periodic case.** For `d = 2`: a word whose partial sums are those of
`chr (2r') (2A')` plus the same `ε ∈ {±1}` at `k₁` and `k₁ + r'` (`0 < k₁ < r'`), with every
entry `≥ 1`, is the 2-fold repetition of a one-move neighbour of `chr r' A'`; Bf_rep and the
`NormAll` theorem exclude it. -/
theorem periodic_case {r' A' k₁ : ℕ} (hk : 0 < k₁) (hkr : k₁ < r')
    (hq : 3 ^ (2 * r') + 1 < 2 ^ (2 * A')) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {v : ℕ → ℕ}
    (hv1 : ∀ i < 2 * r', 1 ≤ v i)
    (hv : ∀ i < 2 * r', (psum v i : ℤ) = psum (NormGoal.chr (2 * r') (2 * A')) i +
      (if i = k₁ then ε else 0) + (if i = k₁ + r' then ε else 0)) :
    ¬ (2 ^ (2 * A') - 3 ^ (2 * r')) ∣ Bnum (2 * r') v := by
  intro hdiv
  have hr' : 0 < r' := by omega
  have hr2 : 2 ≤ r' := by omega
  simp only [psum_chr_two] at hv
  have hcA : ∀ j, (j + r') * A' / r' = j * A' / r' + A' := fun j => by
    rw [add_mul, mul_comm r' A', Nat.add_mul_div_right _ _ hr']
  have hcr : r' * A' / r' = A' := by rw [mul_comm]; exact Nat.mul_div_cancel _ hr'
  have hlo : ∀ i ≤ r', (psum v i : ℤ) = ((i * A' / r' : ℕ) : ℤ) + (if i = k₁ then ε else 0) := by
    intro i hi
    have := hv i (by omega)
    rw [if_neg (show i ≠ k₁ + r' by omega), add_zero] at this
    exact this
  have hhi : ∀ j < r', (psum v (j + r') : ℤ) =
      ((j * A' / r' : ℕ) : ℤ) + A' + (if j = k₁ then ε else 0) := by
    intro j hj
    have := hv (j + r') (by omega)
    rw [if_neg (show j + r' ≠ k₁ by omega), add_zero, hcA] at this
    rw [this]
    by_cases hj1 : j = k₁
    · rw [if_pos (by omega), if_pos hj1]; push_cast; ring
    · rw [if_neg (by omega), if_neg hj1]; push_cast; ring
  have hvr : psum v r' = A' := by
    have := hlo r' le_rfl
    rw [if_neg (by omega), add_zero, hcr] at this
    exact_mod_cast this
  set w : ℕ → ℕ := fun i => v (i % r') with hw
  have hw_lo : ∀ j ≤ r', psum w j = psum v j := by
    intro j hj
    unfold psum
    apply sum_congr rfl
    intro i hi
    have := mem_range.mp hi
    simp only [hw, Nat.mod_eq_of_lt (show i < r' by omega)]
  have hw_add : ∀ j, psum w (j + r') = psum w j + psum w r' := by
    intro j
    unfold psum
    rw [add_comm j r', sum_range_add, add_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    simp [hw]
  have hpw : ∀ j < 2 * r', psum v j = psum w j := by
    intro j hj
    rcases lt_or_ge j r' with h | h
    · exact (hw_lo j h.le).symm
    · obtain ⟨j0, rfl⟩ : ∃ j0, j = j0 + r' := ⟨j - r', by omega⟩
      rw [hw_add, hw_lo j0 (by omega), hw_lo r' le_rfl]
      have a := hhi j0 (by omega)
      have b := hlo j0 (by omega)
      have : (psum v (j0 + r') : ℤ) = psum v j0 + psum v r' := by
        rw [a, b, hvr]; push_cast; ring
      exact_mod_cast this
  have hBvw : Bnum (2 * r') v = Bnum (2 * r') w := by
    unfold Bnum; apply sum_congr rfl; intro i hi; rw [hpw i (mem_range.mp hi)]
  have hrep : Bnum (2 * r') w = Sg (2 ^ A') (3 ^ r') 2 * Bnum r' w := by
    have := Bf_rep (f := psum w) (n := r') (P := A')
      (fun j => by rw [hw_add, hw_lo r' le_rfl, hvr]) 2
    unfold Bf at this; unfold Bnum; exact this
  have hVU := block_lt (d := 2) (by norm_num) hq
  have hqn : 2 ^ (2 * A') - 3 ^ (2 * r') = Sg (2 ^ A') (3 ^ r') 2 * (2 ^ A' - 3 ^ r') := by
    have : ((2 ^ (2 * A') - 3 ^ (2 * r') : ℕ) : ℤ) =
        ((Sg (2 ^ A') (3 ^ r') 2 * (2 ^ A' - 3 ^ r') : ℕ) : ℤ) := by
      rw [q_rep (by omega)]; push_cast [Nat.cast_sub hVU.le]; ring
    exact_mod_cast this
  have hSpos : 0 < Sg (2 ^ A') (3 ^ r') 2 := by
    have := one_lt_Sg (U := 2 ^ A') (V := 3 ^ r') (d := 2)
      (Nat.le_of_lt_succ (by have : 1 ≤ 3 ^ r' := Nat.one_le_pow _ _ (by norm_num); omega))
      (dvd_pow_self 2 (by rintro rfl; simp at hVU)) (by rw [Nat.pow_mod]; simp) le_rfl
    omega
  rw [hBvw, hrep, hqn] at hdiv
  have hdw := Nat.dvd_of_mul_dvd_mul_left hSpos hdiv
  have hq' : 3 ^ r' + 1 < 2 ^ A' := by
    rcases lt_or_eq_of_le (show 3 ^ r' + 1 ≤ 2 ^ A' by omega) with h | h
    · exact h
    · have := NormAll.pow_two_eq_three_pow_succ (a := A') (b := r') (by omega) h.symm; omega
  have hchr : ∀ j, NormGoal.chr r' A' j = (j + 1) * A' / r' - j * A' / r' := fun j => rfl
  have hstep : ∀ j, psum v (j + 1) = psum v j + v j := fun j => by simp [psum, sum_range_succ]
  rcases hε with rfl | rfl
  · -- ε = +1 : slide one unit from k₁ to k₁ - 1
    have h2 : 2 ≤ NormGoal.chr r' A' k₁ := by
      have a := hlo k₁ hkr.le
      have b := hlo (k₁ + 1) (by omega)
      rw [if_pos rfl] at a
      rw [if_neg (by omega), add_zero] at b
      have c := hstep k₁
      have d := hv1 k₁ (by omega)
      rw [hchr]
      have : ((k₁ + 1) * A' / r' : ℕ) = k₁ * A' / r' + 1 + v k₁ := by
        have : (((k₁ + 1) * A' / r' : ℕ) : ℤ) = ((k₁ * A' / r' : ℕ) : ℤ) + 1 + v k₁ := by
          rw [← b, c, Nat.cast_add, a]
        exact_mod_cast this
      omega
    set u := slide (NormGoal.chr r' A') k₁ (k₁ - 1) with hu
    have hmove : OneMove r' (NormGoal.chr r' A') u :=
      Or.inr ⟨k₁, hkr, h2, k₁ - 1, Or.inr (by rw [Nat.sub_add_cancel hk, Nat.mod_eq_of_lt hkr]),
        by omega, by omega, rfl⟩
    have hne : ∃ j < r', u j ≠ NormGoal.chr r' A' j :=
      ⟨k₁, hkr, by rw [hu]; unfold slide; rw [if_pos rfl]; omega⟩
    have hBu : Bnum r' u = Bnum r' w := by
      unfold Bnum; apply sum_congr rfl; intro i hi
      have hi' := mem_range.mp hi
      have e1 := psum_slide (w := NormGoal.chr r' A') (j := k₁) (k := k₁ - 1) (by omega) (by omega) i
      rw [psum_chr, ← hu] at e1
      have e2 := hlo i hi'.le
      rw [hw_lo i hi'.le]
      have : psum u i = psum v i := by
        have : (psum u i : ℤ) = psum v i := by
          rw [e2]
          split_ifs at e1 ⊢ <;> omega
        exact_mod_cast this
      rw [this]
    exact NormAll.no_cycle_one_move_christoffel_all r' A' hr2 hq' u hmove hne (hBu ▸ hdw)
  · -- ε = -1 : slide one unit from k₁ - 1 to k₁
    have h2 : 2 ≤ NormGoal.chr r' A' (k₁ - 1) := by
      have a := hlo k₁ hkr.le
      have b := hlo (k₁ - 1) (by omega)
      rw [if_pos rfl] at a
      rw [if_neg (by omega), add_zero] at b
      have c := hstep (k₁ - 1)
      rw [Nat.sub_add_cancel hk] at c
      have d := hv1 (k₁ - 1) (by omega)
      rw [hchr, Nat.sub_add_cancel hk]
      have : (k₁ * A' / r' : ℕ) = (k₁ - 1) * A' / r' + v (k₁ - 1) + 1 := by
        have : ((k₁ * A' / r' : ℕ) : ℤ) = (((k₁ - 1) * A' / r' : ℕ) : ℤ) + v (k₁ - 1) + 1 := by
          have := a; rw [c, Nat.cast_add, b] at this; linarith
        exact_mod_cast this
      omega
    set u := slide (NormGoal.chr r' A') (k₁ - 1) k₁ with hu
    have hmove : OneMove r' (NormGoal.chr r' A') u :=
      Or.inr ⟨k₁ - 1, by omega, h2, k₁, Or.inl (by rw [Nat.sub_add_cancel hk, Nat.mod_eq_of_lt hkr]),
        hkr, by omega, rfl⟩
    have hne : ∃ j < r', u j ≠ NormGoal.chr r' A' j :=
      ⟨k₁ - 1, by omega, by rw [hu]; unfold slide; rw [if_pos rfl]; omega⟩
    have hBu : Bnum r' u = Bnum r' w := by
      unfold Bnum; apply sum_congr rfl; intro i hi
      have hi' := mem_range.mp hi
      have e1 := psum_slide (w := NormGoal.chr r' A') (j := k₁ - 1) (k := k₁) (by omega) (by omega) i
      rw [psum_chr, ← hu] at e1
      have e2 := hlo i hi'.le
      rw [hw_lo i hi'.le]
      have : psum u i = psum v i := by
        have : (psum u i : ℤ) = psum v i := by
          rw [e2]
          split_ifs at e1 ⊢ <;> omega
        exact_mod_cast this
      rw [this]
    exact NormAll.no_cycle_one_move_christoffel_all r' A' hr2 hq' u hmove hne (hBu ▸ hdw)

/-- `r = d r'`, `A = d A'` with `d = gcd(A, r)`, `r' > 0`. -/
theorem gcd_decomp {r A : ℕ} (hr : 0 < r) :
    ∃ r' A', r = Nat.gcd A r * r' ∧ A = Nat.gcd A r * A' ∧ 0 < r' := by
  obtain ⟨r', hr'⟩ := Nat.gcd_dvd_right A r
  obtain ⟨A', hA'⟩ := Nat.gcd_dvd_left A r
  refine ⟨r', A', hr', hA', ?_⟩
  rcases Nat.eq_zero_or_pos r' with h | h
  · rw [h, mul_zero] at hr'; omega
  · exact h

/-- **T1: every two-site `±1` perturbation of `chr r A` is excluded when
`gcd(A, r) ≥ 2`.** Let `d = gcd(A, r) ≥ 2` and `3^r + 1 < 2^A`. If every entry of `v` below `r`
is `≥ 1` and the partial sums of `v` equal those of `chr r A` plus `ε₁ ∈ {±1}` at `k₁` and
`ε₂ ∈ {±1}` at `k₂` (`0 < k₁ < k₂ < r`), agreeing elsewhere below `r`, then
`(2^A - 3^r) ∤ B(v)`. All sign patterns (right/right, left/left, mixed), any distance; no
size hypothesis on `r` or `A`. Proof: modulo Solomon's cofactor
`S_d = Σ_{s<d} U^s V^{d-1-s}` (`U = 2^{A/d}`, `V = 3^{r/d}`; Solomon 2026, Prop. 6.3 is the
one-move case) the difference `B(v) - B(chr)` is a two-monomial `κ₁3^β + κ₂2^α`, which after
folding is too small to be a nonzero multiple of `S_d ≥ U^{d-1} + V^{d-1}` (`core_cofactor`),
except `d = 2`, distance `r/2`, equal signs: then `v` is a 2-fold repetition of a one-move
neighbour of `chr (r/2) (A/2)`, excluded by `NormAll` (`periodic_case`). -/
theorem no_cycle_two_site_noncoprime (r A : ℕ) (hd : 2 ≤ Nat.gcd A r) (hq : 3 ^ r + 1 < 2 ^ A)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h12 : k₁ < k₂) (h2 : k₂ < r) (ε₁ ε₂ : ℤ)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (v : ℕ → ℕ) (hv1 : ∀ i < r, 1 ≤ v i)
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r A) i + (if i = k₁ then ε₁ else 0) +
      (if i = k₂ then ε₂ else 0)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  obtain ⟨r', A', hr', hA', hr'0⟩ := gcd_decomp (A := A) (show 0 < r by omega)
  obtain ⟨hd2, hk, hεe⟩ := two_site_reduce hr' hA' hd hr'0 hq h1 h12 h2 hε₁ hε₂ hv hdiv
  rw [hd2] at hr' hA'
  subst hεe hk hr' hA'
  exact periodic_case h1 (by omega) hq hε₁ hv1 hv hdiv

/-- **T2: two right flips for ALL `(r, A)`.** `NormFlips`'
`NormFlips.no_cycle_two_right_flips_all` without the coprimality hypothesis (`r ≥ 2325`,
`3^r + 1 < 2^A`, `A < 2r`, entries `≥ 1`): if the partial sums of `v` are those of `chr r A`
plus one at two distinct sites `k₁ ≠ k₂` in `(0, r)` and agree elsewhere below `r`, then
`(2^A - 3^r) ∤ B(v)`. The up-site hypotheses `hs1`, `hs2` are needed in the coprime branch
(`NormFlips`' proof uses them via `omega`; correction recorded in `NormCycleAll`, see
`NormCycleAll.cycle_two_right_flips_nonadj` for a cycle form deriving them from validity). -/
theorem no_cycle_two_right_flips_allRA (r A : ℕ) (hr : 2325 ≤ r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r) (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r)
    (h2' : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : r ≤ k₁ * A % r + A % r) (hs2 : r ≤ k₂ * A % r + A % r)
    (v : ℕ → ℕ) (hv1 : ∀ i < r, 1 ≤ v i)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r A) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hdpos : 0 < Nat.gcd A r := Nat.gcd_pos_of_pos_right _ (by omega)
  rcases Nat.lt_or_ge (Nat.gcd A r) 2 with hd1 | hd2
  · exact NormFlips.no_cycle_two_right_flips_all r A hr (show Nat.gcd A r = 1 by omega) hq hA
      k₁ k₂ h1 h1r h2' h2r hne hs1 hs2 v hv
  · have key : ∀ a b : ℕ, 0 < a → a < b → b < r →
        (∀ i < r, psum v i = psum (NormGoal.chr r A) i + (if i = a ∨ i = b then 1 else 0)) →
        ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
      intro a b ha hab hb hv'
      refine no_cycle_two_site_noncoprime r A hd2 hq a b ha hab hb 1 1 (Or.inl rfl) (Or.inl rfl)
        v hv1 (fun i hi => ?_)
      rw [hv' i hi]
      by_cases e1 : i = a
      · rw [if_pos (Or.inl e1), if_pos e1, if_neg (by omega)]; push_cast; ring
      · by_cases e2 : i = b
        · rw [if_pos (Or.inr e2), if_neg e1, if_pos e2]; push_cast; ring
        · rw [if_neg (by tauto), if_neg e1, if_neg e2]; push_cast; ring
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key k₁ k₂ h1 h h2r hv
    · exact key k₂ k₁ h2' h h1r (fun i hi => by rw [hv i hi]; exact congrArg _ (if_congr or_comm rfl rfl))

section Cycle
open CollatzProof

/-- **Cycle form of T1.** No positive `T`-cycle with `r` odd steps and period `L`,
`gcd(L, r) ≥ 2`, has a valuation word whose partial sums differ from those of `chr r L` by
`±1` at exactly two sites `0 < k₁ < k₂ < r`. -/
theorem cycle_two_site_noncoprime {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hd : 2 ≤ Nat.gcd L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h12 : k₁ < k₂) (h2 : k₂ < r) (ε₁ ε₂ : ℤ)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r L) i + (if i = k₁ then ε₁ else 0) +
      (if i = k₂ then ε₂ else 0)) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  exact no_cycle_two_site_noncoprime r L hd hq k₁ k₂ h1 h12 h2 ε₁ ε₂ hε₁ hε₂ v hv1 hv hdiv

/-- **Cycle form of T2.** No positive `T`-cycle (period `L`, `r ≥ 2325` odd steps, `L < 2r`,
no coprimality) has a valuation word that is two right flips from `chr r L`. -/
theorem cycle_two_right_flips_allRA {m L r : ℕ} {v : ℕ → ℕ} (hr : 2325 ≤ r)
    (hL2 : L < 2 * r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : r ≤ k₁ * L % r + L % r) (hs2 : r ≤ k₂ * L % r + L % r)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) :
    False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_two_right_flips_allRA r L hr hq hL2 k₁ k₂ h1 h1r h2 h2r hne hs1 hs2 v hv1 hv hdiv

end Cycle
end CollatzSearch.NormCofactor

#print axioms CollatzSearch.NormCofactor.core_cofactor
#print axioms CollatzSearch.NormCofactor.two_site_reduce
#print axioms CollatzSearch.NormCofactor.periodic_case
#print axioms CollatzSearch.NormCofactor.no_cycle_two_site_noncoprime
#print axioms CollatzSearch.NormCofactor.no_cycle_two_right_flips_allRA
#print axioms CollatzSearch.NormCofactor.cycle_two_site_noncoprime
#print axioms CollatzSearch.NormCofactor.cycle_two_right_flips_allRA
