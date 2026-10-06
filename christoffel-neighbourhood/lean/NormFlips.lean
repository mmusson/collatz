import NormFilter

/-!
# all two right flips, and `k` right flips (DIRECTIVES 2(b))

Setting as in `NormTwo`: `r ≥ 2325`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`, `A < 2r`,
`q = 2^A - 3^r`, `g^r = 2`, `θ = 2^{1/r}`, `X = θ^{2(A-r)}`, `p_k = r - 1 - (k A mod r)`.
A right flip at an up-site `k` raises the partial sum `A_k` by one.

* `no_cycle_two_right_flips_all` (T2): two right flips anywhere. Removes the corner hypothesis
  of `NormTwo.no_cycle_two_right_flips` (`NormTwo`). Off the corner (`3a ≤ r`) it uses `NormTwo`'s
  `core_right`. In the corner it uses the filtered engine (`NormFilter.flips_engine`, Gram
  bound `Q_eff ≤ 1.2578 + 3.0022 X`). The wrap case `b = r - 2` (`A = 2r - 1`) uses
  `wrap_engine`.
* `no_cycle_k_right_flips` (T3): any set `K` of at least two up-sites with
  `Σ_{k∈K} 4^{p_k/r} ≤ 4.9`. Reduction to `1 + (g-1)Σ_{p∈P} g^p = 0`. Every `p ≤ r-3` because
  `|K| ≥ 2`. Strong induction on `|P|` shifts away `p = 0`, since `g` is a unit. Then
  `Q_eff ≤ 8.61 < 8.76`. Examples: three flips with all `p ≤ 0.354 r`, or four flips with all
  `p ≤ 0.146 r`. These are the first exclusions beyond two moves.
* `cycle_two_right_flips_all`, `cycle_k_right_flips`: the same statements for actual positive
  `T`-cycles, via `NormTwo.cycle_q`.

Novelty, which still needs an adversarial check: the defect area of a right flip is `E = p`.
Mghirbi's coprime bound covers only `E ≤ 1.536 r^{2/3}`, so these results are plausibly new
only in the large-`E` regime. Solomon and Mghirbi do not treat right flips. Knight, Lebel,
Mghirbi and Solomon are credited for the norm framework and for the left-flip/E-small cases.

Limits: these are word-level results only, for coprime `(r, A)`, `r ≥ 2325` and `A < 2r`.
They are not a milestone. Mixed up/down pairs, stacked moves and three down moves remain
open; the one-tap and Szegő filters fail there.
-/

namespace CollatzSearch.NormFlips
open CollatzSearch.NormGoal CollatzSearch.NormReduce CollatzSearch.NormSparse
  CollatzSearch.NormTwo CollatzSearch.NormFilter Finset

section Finish
variable {r A : ℕ} {θ : ℝ}

theorem t_le (hr : 2325 ≤ r) (hθ : 0 < θ) (hθr : θ ^ r = 2) : θ ^ 2 ≤ 1 + 3 / 2325 :=
  (theta_sq_le (by omega) hθ hθr).trans (by linarith [eps_le hr])

/-- Size finish for the flip engine: `S ≤ 8` and (`S ≤ 4.9` or `S ≤ 2X`). -/
theorem finish_flips (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hAr : r ≤ A)
    (hθ : 0 < θ) (hθr : θ ^ r = 2) {S : ℝ} (hS0 : 0 ≤ S) (hS8 : S ≤ 8)
    (hS : S ≤ 49 / 10 ∨ S ≤ 2 * θ ^ (2 * (A - r)))
    (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤
      (1 + θ ^ 2 / 4 + (1 + θ ^ 2 / 4 + θ ^ 4 / 4) * S + (1 + (1 + θ ^ 2) * S) / r) ^ r) : False := by
  have hr0 : 0 < r := by omega
  have ht := t_le hr hθ hθr
  have ht1 : (1:ℝ) ≤ θ ^ 2 := one_le_pow₀ (theta_ge_one hr0 hθ hθr)
  have h4 : θ ^ 4 = (θ ^ 2) ^ 2 := by ring
  have hK : 1 + θ ^ 2 / 4 + θ ^ 4 / 4 ≤ 1 + (1 + 3 / 2325) / 4 + (1 + 3 / 2325) ^ 2 / 4 := by
    rw [h4]; nlinarith
  have hKS := mul_le_mul_of_nonneg_right hK hS0
  have hr' : (2325:ℝ) ≤ r := by exact_mod_cast hr
  have hnum : 0 ≤ 1 + (1 + θ ^ 2) * S := by positivity
  have hD : (1 + (1 + θ ^ 2) * S) / r ≤ 18 / 2325 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 1 + (1 + θ ^ 2) * S ≤ 18 := by nlinarith
    nlinarith
  have hQ0 : 0 ≤ 1 + θ ^ 2 / 4 + (1 + θ ^ 2 / 4 + θ ^ 4 / 4) * S + (1 + (1 + θ ^ 2) * S) / r := by
    positivity
  refine size_contra hr hq hAr hθ hθr hQ0 hQ (fun hii => ?_) (fun hi => ?_)
  · have hX := X_le hr0 hθ hθr hAr hii
    have hS' : S ≤ 49 / 10 := by
      rcases hS with h | h
      · exact h
      · have := eps_le hr; nlinarith
    nlinarith
  · have hX := X_ge hr0 hθ hθr hAr hi
    rcases hS with h | h
    · nlinarith
    · nlinarith

/-- Size finish for the wrap engine (`A = 2r - 1`, `X = θ^{2(r-1)}`, `X θ^2 = 4`). -/
theorem finish_wrap (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hAr : r ≤ A)
    (hθ : 0 < θ) (hθr : θ ^ r = 2) {S Y X : ℝ} (hS0 : 0 ≤ S) (hY0 : 0 ≤ Y) (hX : X = θ ^ (2 * (A - r)))
    (hXt : X * θ ^ 2 = 4) (hSX : S ≤ X) (hYX : Y ≤ X)
    (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤
      ((16 + θ ^ 2 + (4 + θ ^ 2 + θ ^ 4) * S + X + 4 * Y) / 4 + (1 + (1 + θ ^ 2) * S + X + Y) / r) ^ r) :
    False := by
  have hr0 : 0 < r := by omega
  have ht := t_le hr hθ hθr
  have ht1 : (1:ℝ) ≤ θ ^ 2 := one_le_pow₀ (theta_ge_one hr0 hθ hθr)
  have h4 : θ ^ 4 = (θ ^ 2) ^ 2 := by ring
  have hX4 : X ≤ 4 := by nlinarith
  have hX3 : 399 / 100 ≤ X := by nlinarith
  have hK : 4 + θ ^ 2 + θ ^ 4 ≤ 4 + (1 + 3 / 2325) + (1 + 3 / 2325) ^ 2 := by rw [h4]; nlinarith
  have hKS := mul_le_mul_of_nonneg_right hK hS0
  have hr' : (2325:ℝ) ≤ r := by exact_mod_cast hr
  have hD : (1 + (1 + θ ^ 2) * S + X + Y) / r ≤ 18 / 2325 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 1 + (1 + θ ^ 2) * S + X + Y ≤ 18 := by nlinarith
    have : 0 ≤ 1 + (1 + θ ^ 2) * S + X + Y := by positivity
    nlinarith
  have hQ0 : 0 ≤ (16 + θ ^ 2 + (4 + θ ^ 2 + θ ^ 4) * S + X + 4 * Y) / 4 +
      (1 + (1 + θ ^ 2) * S + X + Y) / r := by positivity
  refine size_contra hr hq hAr hθ hθr hQ0 hQ (fun hii => ?_) (fun hi => ?_)
  · have hX' := X_le hr0 hθ hθr hAr hii
    have := eps_le hr
    rw [← hX] at hX'
    nlinarith
  · rw [← hX]
    nlinarith

end Finish

section Core
variable {r A : ℕ}

/-- Core of two right flips, all positions (no corner hypothesis): from
`G + (g-1)(G g^a + G g^b) = 0` with `a < b`, `b + 1 ≤ A - r`, contradiction. -/
theorem core_right_all (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r)
    {g G : ZMod (2 ^ A - 3 ^ r)} (h2 : g ^ r = 2) (hGu : IsUnit G)
    {a b : ℕ} (hab : a < b) (hbA : b + 1 ≤ A - r)
    (heq : G + (g - 1) * (G * g ^ a + G * g ^ b) = 0) : False := by
  by_cases ha3 : 3 * a ≤ r
  · exact core_right hr hq hA h2 hGu hab ha3 hbA heq
  have hAr : r < A := r_lt_A hq
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  have hr0 : 0 < r := by omega
  obtain ⟨θ, hθ, hθr⟩ := exists_theta hr0
  have mono := fun {a b : ℕ} (h : a ≤ b) => theta_pow_mono hr0 hθ hθr h
  have ht := t_le hr hθ hθr
  have ht2 : θ ^ 2 ≤ 2 := by linarith
  have hβ : 1 + (g - 1) * (g ^ a + g ^ b) = 0 :=
    hGu.mul_right_eq_zero.mp (show G * (1 + (g - 1) * (g ^ a + g ^ b)) = 0 by
      linear_combination heq)
  have h4r : θ ^ (2 * r) = 4 := by rw [pow_mul', hθr]; norm_num
  have hX4 : θ ^ (2 * (A - r)) ≤ 4 := by rw [← h4r]; exact mono (by omega)
  by_cases hb3 : b + 3 ≤ r
  · have hP : ∀ p ∈ ({a, b} : Finset ℕ), 1 ≤ p ∧ p + 3 ≤ r := by
      intro p hp; simp only [mem_insert, mem_singleton] at hp; omega
    have hE := flips_engine hq1 (by omega) g h2 {a, b} hP
      (by rw [sum_pair hab.ne]; exact hβ) θ hθ hθr ht2
    rw [sum_pair hab.ne] at hE
    have h1 := mono (show a ≤ A - r by omega)
    have h2' := mono (show b ≤ A - r by omega)
    exact finish_flips hr hq hAr.le hθ hθr (by positivity) (by linarith) (Or.inr (by linarith)) hE
  · have hb : b = r - 2 := by omega
    have hρ : A - r = r - 1 := by omega
    subst hb
    have hP : ∀ p ∈ ({a} : Finset ℕ), 1 ≤ p ∧ p + 3 ≤ r := by
      intro p hp; simp only [mem_singleton] at hp; omega
    have hE := wrap_engine hq1 (by omega) g h2 {a} hP (by rw [sum_singleton]; exact hβ)
      θ hθ hθr ht2
    rw [sum_singleton] at hE
    have h1 := mono (show a ≤ r - 1 by omega)
    have h2' := mono (show r - 2 ≤ r - 1 by omega)
    have hXt : θ ^ (2 * (r - 1)) * θ ^ 2 = 4 := by rw [← pow_add, ← h4r]; congr 1; omega
    exact finish_wrap hr hq hAr.le hθ hθr (by positivity) (by positivity) (by rw [hρ]) hXt h1 h2' hE

/-- `θ = 2^{1/r}` gives `θ^{2m} = 4^{m/r}`. -/
theorem theta_pow_eq {r m : ℕ} (hr : 0 < r) :
    ((2:ℝ) ^ ((r:ℝ)⁻¹)) ^ (2 * m) = (4:ℝ) ^ ((m:ℝ) / r) := by
  rw [← Real.rpow_mul_natCast (by norm_num), show (4:ℝ) = 2 ^ (2:ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num)]
  congr 1; push_cast; field_simp

/-- Core of `k` right flips: no finite `P ⊆ [0, r-3]` with `Σ_P θ^{2p} ≤ 4.9` satisfies
`1 + (g-1) Σ_P g^p = 0` (strong induction on `|P|`, shifting away `p = 0`). -/
theorem core_k (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A)
    {g : ZMod (2 ^ A - 3 ^ r)} (h2 : g ^ r = 2) {θ : ℝ} (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    ∀ n, ∀ P : Finset ℕ, P.card = n → (∀ p ∈ P, p + 3 ≤ r) →
      ∑ p ∈ P, θ ^ (2 * p) ≤ 49 / 10 → 1 + (g - 1) * ∑ p ∈ P, g ^ p = 0 → False := by
  have hAr : r < A := r_lt_A hq
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  have hr0 : 0 < r := by omega
  have hgu := isUnit_g (by omega) hq h2
  have ht := t_le hr hθ hθr
  have ht2 : θ ^ 2 ≤ 2 := by linarith
  have hθ1 := theta_ge_one hr0 hθ hθr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hcard hP hS h
  by_cases h0 : 0 ∈ P
  · set P' := (P.erase 0).image (fun x => x - 1) with hP'
    have hinj : Set.InjOn (fun x => x - 1) (P.erase 0 : Set ℕ) := by
      intro x hx y hy hxy
      simp only [coe_erase, Set.mem_diff, mem_coe, Set.mem_singleton_iff] at hx hy
      simp only at hxy; omega
    have hsplit : ∑ p ∈ P, g ^ p = 1 + ∑ p ∈ P.erase 0, g ^ p := by
      rw [← add_sum_erase P _ h0, pow_zero]
    have hshift : ∑ p ∈ P.erase 0, g ^ p = g * ∑ p ∈ P', g ^ p := by
      rw [hP', sum_image hinj, Finset.mul_sum]
      apply sum_congr rfl; intro x hx
      have := ne_of_mem_erase hx
      rw [← pow_succ']; congr 1; omega
    have hrel : 1 + (g - 1) * ∑ p ∈ P', g ^ p = 0 := by
      apply hgu.mul_right_eq_zero.mp
      rw [hsplit, hshift] at h
      linear_combination h
    have hcard' : P'.card < n := by
      calc P'.card ≤ (P.erase 0).card := card_image_le
        _ < P.card := card_erase_lt_of_mem h0
        _ = n := hcard
    refine ih P'.card hcard' P' rfl ?_ ?_ hrel
    · intro p hp
      rw [hP', mem_image] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      have := hP x (mem_of_mem_erase hx); omega
    · rw [hP', sum_image hinj]
      calc ∑ x ∈ P.erase 0, θ ^ (2 * (x - 1)) ≤ ∑ x ∈ P.erase 0, θ ^ (2 * x) :=
            sum_le_sum fun x _ => theta_pow_mono hr0 hθ hθr (by omega)
        _ ≤ ∑ x ∈ P, θ ^ (2 * x) := sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            (fun _ _ _ => by positivity)
        _ ≤ 49 / 10 := hS
  · have hP1 : ∀ p ∈ P, 1 ≤ p ∧ p + 3 ≤ r := by
      intro p hp; refine ⟨?_, hP p hp⟩
      rcases Nat.eq_zero_or_pos p with h' | h'
      · subst h'; exact absurd hp h0
      · exact h'
    have hE := flips_engine hq1 (by omega) g h2 P hP1 h θ hθ hθr ht2
    exact finish_flips hr hq hAr.le hθ hθr (sum_nonneg fun _ _ => by positivity) (by linarith)
      (Or.inl hS) hE

end Core

section Main

/-- **All two right flips (closes the up/up corner left open in `NormTwo`).** Let
`r ≥ 2325`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`, `A < 2r`. If the partial sums of `v` equal those
of the Christoffel word `chr r A` plus one at two distinct up-sites `k₁ ≠ k₂` in `(0, r)`
(`r ≤ k A mod r + A mod r`) and agree elsewhere below `r`, then `(2^A - 3^r) ∤ B(v)`.
No corner hypothesis: subsumes `NormTwo.no_cycle_two_right_flips`. The up-site hypotheses
`_hs1`, `_hs2` ARE used, implicitly, by the `omega` calls supplying `b + 1 ≤ A - r` (the underscore
names hid this; see `NormCycleAll.up_site_of_valid`). For
`gcd(A, r) ≥ 2` see `NormCofactor.no_cycle_two_right_flips_allRA`. -/
theorem no_cycle_two_right_flips_all (r A : ℕ) (hr : 2325 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r) (k₁ k₂ : ℕ) (_h1 : 0 < k₁) (h1r : k₁ < r)
    (_h2' : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (_hs1 : r ≤ k₁ * A % r + A % r) (_hs2 : r ≤ k₂ * A % r + A % r)
    (v : ℕ → ℕ) (hv : ∀ i < r, psum v i = psum (NormGoal.chr r A) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  have hnt := nontrivial_q hq
  have hr2 : 2 ≤ r := by omega
  obtain ⟨g, h2, h3⟩ := exists_g (by omega) hcop hq
  have hAr := r_lt_A hq
  have hA1 : 1 ≤ A := by omega
  have hmod := modA hAr hA
  have hK := knight_identity hr2 hcop hq h2 h3
  set G := g ^ ((A - 1) * (r - 1)) with hG
  have hGu : IsUnit G := (isUnit_g (by omega) hq h2).pow _
  have hBv : (Bnum r v : ZMod (2 ^ A - 3 ^ r)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  rw [cast_Bnum] at hBv
  have hBw := cast_Bnum (R := ZMod (2 ^ A - 3 ^ r)) r (NormGoal.chr r A)
  set Fv : ℕ → ZMod (2 ^ A - 3 ^ r) := fun i => 3 ^ (r - 1 - i) * 2 ^ psum v i with hFv
  set Fw : ℕ → ZMod (2 ^ A - 3 ^ r) := fun i => 3 ^ (r - 1 - i) * 2 ^ psum (NormGoal.chr r A) i with hFw
  have hpt : ∀ i ∈ range r, Fv i = Fw i + (if i = k₁ then Fw i else 0) +
      (if i = k₂ then Fw i else 0) := by
    intro i hi
    have hi' := mem_range.mp hi
    have hvi := hv i hi'
    by_cases e1 : i = k₁
    · have e2 : ¬ i = k₂ := by omega
      rw [if_pos (Or.inl e1)] at hvi
      have hp : psum v i = psum (NormGoal.chr r A) i + 1 := by omega
      simp only [hFv, hFw]; rw [hp, if_pos e1, if_neg e2, pow_succ]; ring
    · by_cases e2 : i = k₂
      · rw [if_pos (Or.inr e2)] at hvi
        have hp : psum v i = psum (NormGoal.chr r A) i + 1 := by omega
        simp only [hFv, hFw]; rw [hp, if_neg e1, if_pos e2, pow_succ]; ring
      · rw [if_neg (by tauto)] at hvi
        have hp : psum v i = psum (NormGoal.chr r A) i := by omega
        simp only [hFv, hFw]; rw [hp, if_neg e1, if_neg e2]; ring
  have hsum : (Bnum r v : ZMod (2 ^ A - 3 ^ r)) = ∑ i ∈ range r, Fw i + Fw k₁ + Fw k₂ := by
    rw [cast_Bnum, ← sum_two_pt Fw (mem_range.mpr h1r) (mem_range.mpr h2r)]
    exact sum_congr rfl hpt
  have hF : ∀ k, k < r → Fw k = G * g ^ (r - 1 - k * A % r) :=
    fun k hk => term_chr h2 h3 hA1 hk
  have hsw : ∑ i ∈ range r, Fw i = (Bnum r (NormGoal.chr r A) : ZMod (2 ^ A - 3 ^ r)) := hBw.symm
  rw [hsw, cast_Bnum, hBv, hF k₁ h1r, hF k₂ h2r] at hsum
  have heq : G + (g - 1) * (G * g ^ (r - 1 - k₁ * A % r) + G * g ^ (r - 1 - k₂ * A % r)) = 0 := by
    linear_combination -hK - (g - 1) * hsum
  have hρne : k₁ * A % r ≠ k₂ * A % r := fun h => hne (mod_inj hcop h1r h2r h)
  have hm1 := Nat.mod_lt (k₁ * A) (show 0 < r by omega)
  have hm2 := Nat.mod_lt (k₂ * A) (show 0 < r by omega)
  rcases Nat.lt_or_gt_of_ne (show r - 1 - k₁ * A % r ≠ r - 1 - k₂ * A % r by omega) with hlt | hgt
  · exact core_right_all hr hq hA h2 hGu hlt (by omega) heq
  · exact core_right_all hr hq hA h2 hGu hgt (by omega) (by rw [← heq]; ring)

/-- **`k` right flips with small total weight (first exclusions beyond two
moves).** Let `r ≥ 2325`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`, `A < 2r`, and let `K` be a set of
at least two up-sites `k ∈ (0, r)` (`r ≤ k A mod r + A mod r`) with
`Σ_{k∈K} 4^{p_k/r} ≤ 4.9`, where `p_k = r - 1 - (k A mod r)`. If the partial sums of `v` equal
those of `chr r A` plus one on `K` and agree elsewhere below `r`, then `(2^A - 3^r) ∤ B(v)`.
(E.g. three flips with all `p_k ≤ 0.354 r`, or four with all `p_k ≤ 0.146 r`.) The up-site
hypothesis `_hs` is unused (any set `K` of sites in `(0, r)` works). -/
theorem no_cycle_k_right_flips (r A : ℕ) (hr : 2325 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r) (K : Finset ℕ) (hK2 : 2 ≤ K.card)
    (hKr : ∀ k ∈ K, 0 < k ∧ k < r) (_hs : ∀ k ∈ K, r ≤ k * A % r + A % r)
    (hS : ∑ k ∈ K, (4:ℝ) ^ (((r - 1 - k * A % r : ℕ) : ℝ) / r) ≤ 49 / 10)
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
  have hSP : ∑ p ∈ P, θ ^ (2 * p) ≤ 49 / 10 := by
    rw [hP, sum_image hinj]
    calc ∑ k ∈ K, θ ^ (2 * pk k) = ∑ k ∈ K, (4:ℝ) ^ (((r - 1 - k * A % r : ℕ) : ℝ) / r) :=
          sum_congr rfl fun k _ => theta_pow_eq hr0
      _ ≤ 49 / 10 := hS
  have hrelP : 1 + (g - 1) * ∑ p ∈ P, g ^ p = 0 := by rw [hP, sum_image hinj]; exact hβ
  have hcardP : 2 ≤ P.card := by rw [hP, card_image_of_injOn hinj]; exact hK2
  have hθ1 := theta_ge_one hr0 hθ hθr
  have ht := t_le hr hθ hθr
  have hP3 : ∀ p ∈ P, p + 3 ≤ r := by
    intro p hp
    have hplt : p < r := by
      rw [hP, mem_image] at hp; obtain ⟨k, _, rfl⟩ := hp; simp only [hpk]; omega
    by_contra hcon
    obtain ⟨p', hp', hne⟩ := exists_mem_ne (s := P) (by omega) p
    have hsub : ({p, p'} : Finset ℕ) ⊆ P := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    have hle := sum_le_sum_of_subset_of_nonneg hsub (f := fun p => θ ^ (2 * p))
      (fun _ _ _ => by positivity)
    rw [sum_pair hne.symm] at hle
    have h1 : (1:ℝ) ≤ θ ^ (2 * p') := one_le_pow₀ hθ1
    have hY := theta_pow_mono hr0 hθ hθr (show r - 2 ≤ p by omega)
    have h4r : θ ^ (2 * (r - 2)) * (θ ^ 2) ^ 2 = 4 := by
      rw [← pow_mul, ← pow_add, show 4 = (θ ^ r) ^ 2 by rw [hθr]; norm_num, ← pow_mul]
      congr 1; omega
    have ht1 : (1:ℝ) ≤ θ ^ 2 := one_le_pow₀ hθ1
    have : (θ ^ 2) ^ 2 ≤ (1 + 3 / 2325) ^ 2 := pow_le_pow_left₀ (by positivity) ht 2
    nlinarith [pow_nonneg hθ.le (2 * (r - 2))]
  exact core_k hr hq h2 hθ hθr P.card P rfl hP3 hSP hrelP

end Main

section Cycle
open CollatzProof

/-- **Cycle form of T2.** No positive `T`-cycle (period `L`, `r ≥ 2325` odd steps,
`gcd(L, r) = 1`, `L < 2r`) has a valuation word that is two right flips (at up-sites,
anywhere) from the Christoffel word `chr r L`. (`hs1`, `hs2` are needed; see the word-level
theorem.) -/
theorem cycle_two_right_flips_all {m L r : ℕ} {v : ℕ → ℕ} (hr : 2325 ≤ r) (hcop : Nat.Coprime L r)
    (hL2 : L < 2 * r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : r ≤ k₁ * L % r + L % r) (hs2 : r ≤ k₂ * L % r + L % r)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) : False := by
  obtain ⟨hq, hdiv⟩ := cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_two_right_flips_all r L hr hcop hq hL2 k₁ k₂ h1 h1r h2 h2r hne hs1 hs2 v hv hdiv

/-- **Cycle form of T3.** No positive `T`-cycle (period `L`, `r ≥ 2325` odd steps,
`gcd(L, r) = 1`, `L < 2r`) has a valuation word obtained from `chr r L` by right flips at a
set `K` of at least two up-sites with `Σ_{k∈K} 4^{p_k/r} ≤ 4.9`. -/
theorem cycle_k_right_flips {m L r : ℕ} {v : ℕ → ℕ} (hr : 2325 ≤ r) (hcop : Nat.Coprime L r)
    (hL2 : L < 2 * r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (K : Finset ℕ) (hK2 : 2 ≤ K.card) (hKr : ∀ k ∈ K, 0 < k ∧ k < r)
    (hs : ∀ k ∈ K, r ≤ k * L % r + L % r)
    (hS : ∑ k ∈ K, (4:ℝ) ^ (((r - 1 - k * L % r : ℕ) : ℝ) / r) ≤ 49 / 10)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i ∈ K then 1 else 0)) : False := by
  obtain ⟨hq, hdiv⟩ := cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_k_right_flips r L hr hcop hq hL2 K hK2 hKr hs hS v hv hdiv

end Cycle

end CollatzSearch.NormFlips

#print axioms CollatzSearch.NormFlips.core_right_all
#print axioms CollatzSearch.NormFlips.core_k
#print axioms CollatzSearch.NormFlips.no_cycle_two_right_flips_all
#print axioms CollatzSearch.NormFlips.no_cycle_k_right_flips
#print axioms CollatzSearch.NormFlips.cycle_two_right_flips_all
#print axioms CollatzSearch.NormFlips.cycle_k_right_flips
