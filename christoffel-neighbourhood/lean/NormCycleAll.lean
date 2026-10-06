import NormCofactor
import NormMixed
import CollatzSearch.Crandall
import CollatzSearch.MaxProduct
import CollatzSearch.CRuns
import CollatzSearch.CycleMin
import CollatzSearch.CycleMax


/-!
# hypothesis-free cycle forms (DIRECTIVES 2(a), "all (r, A)")

Every nontrivial positive `T`-cycle automatically satisfies `L < 2r` (Crandall sandwich at the
orbit minimum, which is `≥ 2`) and `L + r ≥ 122703` (our `cycleLengthAtLeast_122703`), hence
`r ≥ 40901 > 2325` (`cycle_params`). So the side hypotheses `r ≥ 2325` and `L < 2r` of the
the earlier files cycle forms are automatic, and are removed here:

* `cycle_two_right_flips_uncond`: two right flips at up-sites, all `gcd(L, r)`;
  `cycle_two_right_flips_nonadj`: any two non-adjacent sites (up-site conditions derived from
  validity by `up_site_of_valid`).
* `cycle_two_left_flips_uncond`: two left flips, all `gcd(L, r)` (the down-site conditions are
  used only when `gcd(L, r) = 1`, via `NormTwo`; `gcd ≥ 2` is `NormCofactor`'s two-site theorem with `ε = -1`);
  `cycle_two_left_flips_nonadj`: any two non-adjacent sites (down-site conditions derived from
  validity by `down_site_of_valid`).
* `cycle_k_right_flips_uncond`: `k` right flips with `Σ 4^{p_k/r} ≤ 4.9`, coprime, no site
  conditions.
* `cycle_mixed_flips_uncond`: `NormMixed` mixed pairs, coprime.
* `exists_odd_point`: every positive cycle has an odd point, so the corollaries (stated for any
  odd point `m`, with `m ≠ 1`) cover every nontrivial positive cycle.
* `no_cycle_k_right_flips'`: `NormFlips`' `k`-flip theorem without its (truly unused) up-site
  hypothesis and without `A < 2r`. NOTE: the `NormFlips`/`NormCofactor` two-right-flip docstrings claim
  `hs1`, `hs2` are unused; that is false (`NormFlips`' `omega` calls use them from the context, for
  `b + 1 ≤ A - r`), so the two-right-flip forms keep them or derive them.

All results are about valuation words close to Christoffel words; they are not milestones and
do not advance `Goal.lean`.
-/

namespace CollatzSearch.NormCycleAll
open CollatzSearch.NormGoal CollatzSearch.NormBridge CollatzProof Finset

/-- Along a cycle word, the number of odd steps among the first `psum v i` steps is `i`
(the first conjunct of the claim in `NormBridge.cycle_word_eq`). -/
theorem oddSteps_psum {m L r : ℕ} {v : ℕ → ℕ} (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) :
    ∀ i ≤ r, oddSteps (psum v i) m = i := by
  intro i
  induction i with
  | zero => intro _; simp [psum, oddSteps]
  | succ i ih =>
    intro hi
    have ih1 := ih (by omega)
    have hvi := hv1 i (by omega)
    have hLi : psum v (i + 1) ≤ L := hL ▸ psum_mono v hi
    rw [psum_succ] at hLi
    have inner : ∀ s, 1 ≤ s → s ≤ v i → oddSteps (psum v i + s) m = i + 1 := by
      intro s hs1 hs2
      induction s with
      | zero => omega
      | succ s ihs =>
        rcases Nat.eq_zero_or_pos s with h0 | hpos
        · subst h0
          have hodd1 : T^[psum v i] m % 2 = 1 :=
            (hodd (psum v i) (by omega)).mpr ⟨i, by omega, rfl⟩
          rw [← add_assoc, add_zero, oddSteps_succ_last, ih1, hodd1]
        · have e1 := ihs hpos (by omega)
          have heven : T^[psum v i + s] m % 2 = 0 := by
            have : ¬ T^[psum v i + s] m % 2 = 1 := by
              rw [hodd _ (by omega)]
              rintro ⟨i', hi', heq⟩
              rcases Nat.lt_or_ge i i' with h | h
              · have := psum_mono v (show i + 1 ≤ i' by omega)
                rw [psum_succ] at this; omega
              · have := psum_mono v h; omega
            omega
          rw [← add_assoc, oddSteps_succ_last, heven, add_zero, e1]
    rw [psum_succ]
    exact inner (v i) hvi le_rfl

/-- **Every positive `T`-cycle has an odd point.** If `n > 0`, `L > 0` and `T^L n = n`, some
`T^j n` with `j < L` is odd (otherwise `n = T^L n = n / 2^L < n`). So the cycle corollaries
below, which quantify over every odd point `m` of a cycle, apply to every positive cycle: the
"orbit starts at an odd time" caveat of the the earlier files bridges is no restriction. -/
theorem exists_odd_point {n L : ℕ} (hn : 0 < n) (hL : 0 < L) (h : T^[L] n = n) :
    ∃ j < L, T^[j] n % 2 = 1 := by
  by_contra hne
  push Not at hne
  have key : ∀ j ≤ L, 2 ^ j * T^[j] n = n := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have he : T^[j] n % 2 = 0 := by have := hne j (by omega); omega
      rw [Function.iterate_succ_apply', T_of_even he]
      calc 2 ^ (j + 1) * (T^[j] n / 2) = 2 ^ j * (2 * (T^[j] n / 2)) := by ring
        _ = 2 ^ j * T^[j] n := by congr 1; omega
        _ = n := ih (by omega)
  have h1 := key L le_rfl
  rw [h] at h1
  have h2 : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  nlinarith

/-- **Cycle parameters (key lemma).** Let `m ≠ 1` be a point of a positive `T`-cycle
of length `L` whose odd steps in the first `L` steps sit exactly at the partial sums
`psum v i`, `i < r` (entries `≥ 1`, `psum v r = L`, `r ≥ 1`). Then `L < 2r` and
`r ≥ 40901`. Proof: the odd count is `r`, so `C^{L+r} m = m` and `L + r ≥ 122703`
(`cycleLengthAtLeast_122703`); the Crandall sandwich at the orbit minimum `m₀ ≥ 2` gives
`2^L m₀^r ≤ (3m₀+1)^r < 4^r m₀^r`, so `L < 2r`, hence `3r > 122703`. -/
theorem cycle_params {m L r : ℕ} {v : ℕ → ℕ} (hr : 1 ≤ r) (hv1 : ∀ i < r, 1 ≤ v i)
    (hL : psum v r = L) (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j))
    (hcyc : T^[L] m = m) (hm : m ≠ 1) : L < 2 * r ∧ 40901 ≤ r := by
  have hS : oddSteps L m = r := by
    have := oddSteps_psum hv1 hL hodd r le_rfl; rwa [hL] at this
  have hLr : r ≤ L := by
    have : ∀ i ≤ r, i ≤ psum v i := by
      intro i
      induction i with
      | zero => intro _; simp [psum]
      | succ i ih =>
        intro hi; rw [psum_succ]; have := ih (by omega); have := hv1 i (by omega); omega
    have := this r le_rfl; omega
  have hL0 : 0 < L := by omega
  have hmodd : m % 2 = 1 := by
    have := (hodd 0 hL0).mpr ⟨0, by omega, by simp [psum]⟩
    simpa using this
  have hm0 : 0 < m := by omega
  have hC : C^[L + r] m = m := by rw [← hS, iterate_C_add_oddSteps, hcyc]
  have hlen := cycleLengthAtLeast_122703 m (L + r) hm0 (by omega) hC hm (by omega) (by omega)
  obtain ⟨a, ha, hmin, _⟩ := exists_cycle_min hL0 hcyc
  obtain ⟨b, _, hmax⟩ := exists_orbit_max T hL0 hcyc
  have hm0a : 0 < T^[a] m := iterate_T_pos hm0 a
  have hsand := (cycle_sandwich (b := b) hcyc hm0a hmin (fun i => by
    rw [← Function.iterate_add_apply]; exact hmax _)).1
  rw [hS] at hsand
  have hx2 : 2 ≤ T^[a] m := by
    by_contra hlt
    have e : T^[a] m = 1 := by omega
    have hxM : T^[L - a] (T^[a] m) = m := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel ha.le, hcyc]
    rw [e] at hxM
    rcases iterate_T_one_mem (L - a) with e' | e' <;> rw [hxM] at e' <;> omega
  set x := T^[a] m with hx
  have h1 : (3 * x + 1) ^ r < (4 * x) ^ r := Nat.pow_lt_pow_left (by omega) (by omega)
  have h2 : 2 ^ L * x ^ r < 2 ^ (2 * r) * x ^ r := by
    calc 2 ^ L * x ^ r ≤ (3 * x + 1) ^ r := hsand
      _ < (4 * x) ^ r := h1
      _ = 2 ^ (2 * r) * x ^ r := by rw [mul_pow, pow_mul]; norm_num
  have h3 : 2 ^ L < 2 ^ (2 * r) := lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
  have h4 : L < 2 * r := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
  omega


section Word
open CollatzSearch.NormReduce CollatzSearch.NormSparse CollatzSearch.NormTwo
  CollatzSearch.NormFilter CollatzSearch.NormFlips

/-- `NormFlips`' `NormFlips.no_cycle_k_right_flips` without its unused up-site hypothesis and
without `A < 2r` (both checked unused by recompiling `NormFlips`' proof without them): any set `K`
of at least two sites in `(0, r)` with `Σ_{k∈K} 4^{p_k/r} ≤ 4.9`. -/
theorem no_cycle_k_right_flips' (r A : ℕ) (hr : 2325 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (K : Finset ℕ) (hK2 : 2 ≤ K.card)
    (hKr : ∀ k ∈ K, 0 < k ∧ k < r)
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

end Word

section Uncond

/-- `gcd(L, r) < 2` with `r > 0` means coprime. -/
theorem coprime_of_gcd_lt_two {L r : ℕ} (hr : 0 < r) (h : Nat.gcd L r < 2) : Nat.Coprime L r := by
  have := Nat.gcd_pos_of_pos_right L hr
  unfold Nat.Coprime; omega

/-- **Up-site from validity.** If `r < A < 2r`, all entries of `v` below `r` are `≥ 1`,
`psum v r = A`, and the partial sums of `v` are those of `chr r A` plus `[S i]`, then every
flip site `k < r` whose successor `k + 1` is not a flip site is an up-site
(`r ≤ kA mod r + A mod r`, i.e. `chr k = 2`): indeed `v k = chr k - 1 ≥ 1`. -/
theorem up_site_of_valid {r A : ℕ} {v : ℕ → ℕ} (hrA : r < A) (hA : A < 2 * r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = A) (S : ℕ → Prop) [DecidablePred S]
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r A) i + (if S i then 1 else 0))
    {k : ℕ} (hk : k < r) (hSk : S k) (hSk1 : ¬ S (k + 1)) : r ≤ k * A % r + A % r := by
  have hr0 : 0 < r := by omega
  have hdiv : A / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hc := NormReduce.chr_eq (A := A) hr0 k
  have hvk := hv1 k hk
  have e1 := hv k hk
  rw [if_pos hSk] at e1
  have e2 : psum v (k + 1) = psum (NormGoal.chr r A) (k + 1) := by
    rcases Nat.lt_or_ge (k + 1) r with h | h
    · have := hv (k + 1) h; rw [if_neg hSk1] at this; exact this
    · have hk1 : k + 1 = r := by omega
      rw [hk1, hL, NormReduce.psum_chr, Nat.mul_div_cancel_left A hr0]
  rw [psum_succ, psum_succ] at e2
  rw [hdiv] at hc
  split_ifs at hc with h
  · exact h
  · omega

/-- **Two right flips, unconditional cycle form.** `NormCofactor`'s
`NormCofactor.cycle_two_right_flips_allRA` with `r ≥ 2325` and `L < 2r` removed (replaced by
`m ≠ 1`): no positive `T`-cycle point `m ≠ 1` (any `gcd(L, r)`) has a valuation word whose
partial sums are those of `chr r L` plus one at two distinct up-sites in `(0, r)`. (The
up-site hypotheses ARE used, by `omega` inside `NormFlips`' proof, contrary to the `NormFlips`/`NormCofactor`
docstrings; see `cycle_two_right_flips_nonadj` for a version without them.) -/
theorem cycle_two_right_flips_uncond {m L r : ℕ} {v : ℕ → ℕ}
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : r ≤ k₁ * L % r + L % r) (hs2 : r ≤ k₂ * L % r + L % r)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) :
    False := by
  obtain ⟨hL2, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  exact NormCofactor.cycle_two_right_flips_allRA (by omega) hL2 hv1 hL hodd hcyc k₁ k₂ h1 h1r
    h2 h2r hne hs1 hs2 hv

/-- **Two non-adjacent right flips, unconditional cycle form, no site conditions (round
124).** No positive `T`-cycle point `m ≠ 1` (any `gcd(L, r)`, no size hypothesis) has a
valuation word whose partial sums are those of `chr r L` plus one at two distinct,
non-adjacent sites in `(0, r)`: the up-site conditions follow from validity
(`up_site_of_valid`). -/
theorem cycle_two_right_flips_nonadj {m L r : ℕ} {v : ℕ → ℕ}
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hadj1 : k₁ + 1 ≠ k₂) (hadj2 : k₂ + 1 ≠ k₁)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) :
    False := by
  obtain ⟨hL2, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨hq, _⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  have hrL := NormReduce.r_lt_A hq
  have hs1 := up_site_of_valid (S := fun i => i = k₁ ∨ i = k₂) hrL hL2 hv1 hL hv h1r
    (Or.inl rfl) (by omega)
  have hs2 := up_site_of_valid (S := fun i => i = k₁ ∨ i = k₂) hrL hL2 hv1 hL hv h2r
    (Or.inr rfl) (by omega)
  exact cycle_two_right_flips_uncond hv1 hL hodd hcyc hm k₁ k₂ h1 h1r h2 h2r hne hs1 hs2 hv

/-- **Two left flips, unconditional cycle form.** No positive `T`-cycle point
`m ≠ 1` (any `gcd(L, r)`, no size hypothesis) has a valuation word whose partial sums are
those of `chr r L` minus one at two distinct sites in `(0, r)` that are down-sites
(`k L mod r < L mod r`). The down-site conditions are used only when `gcd(L, r) = 1`. -/
theorem cycle_two_left_flips_uncond {m L r : ℕ} {v : ℕ → ℕ}
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : k₁ * L % r < L % r) (hs2 : k₂ * L % r < L % r)
    (hv : ∀ i < r, psum v i + (if i = k₁ ∨ i = k₂ then 1 else 0) = psum (NormGoal.chr r L) i) :
    False := by
  obtain ⟨hL2, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  rcases Nat.lt_or_ge (Nat.gcd L r) 2 with hd | hd
  · exact NormTwo.cycle_two_left_flips (by omega) (coprime_of_gcd_lt_two (by omega) hd) hL2 hv1
      hL hodd hcyc k₁ k₂ h1 h1r h2 h2r hne hs1 hs2 hv
  · have key : ∀ a b : ℕ, 0 < a → a < b → b < r →
        (∀ i < r, psum v i + (if i = a ∨ i = b then 1 else 0) = psum (NormGoal.chr r L) i) →
        False := by
      intro a b ha hab hb hv'
      refine NormCofactor.cycle_two_site_noncoprime (by omega) hd hv1 hL hodd hcyc a b ha hab hb
        (-1) (-1) (Or.inr rfl) (Or.inr rfl) (fun i hi => ?_)
      have := hv' i hi
      by_cases e1 : i = a
      · rw [if_pos (Or.inl e1)] at this; rw [if_pos e1, if_neg (by omega)]; omega
      · by_cases e2 : i = b
        · rw [if_pos (Or.inr e2)] at this; rw [if_neg e1, if_pos e2]; omega
        · rw [if_neg (by tauto)] at this; rw [if_neg e1, if_neg e2]; omega
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key k₁ k₂ h1 h h2r hv
    · exact key k₂ k₁ h2 h h1r (fun i hi => by
        rw [← hv i hi]; exact congrArg _ (if_congr or_comm rfl rfl))

/-- **Down-site from validity.** If `r < A < 2r`, entries of `v` below `r` are `≥ 1`, and the
partial sums of `v` are those of `chr r A` minus `[S i]`, then every flip site `0 < k < r`
whose predecessor `k - 1` is not a flip site is a down-site (`kA mod r < A mod r`, i.e.
`chr (k-1) = 2`): indeed `v (k-1) = chr (k-1) - 1 ≥ 1`. -/
theorem down_site_of_valid {r A : ℕ} {v : ℕ → ℕ} (hrA : r < A) (hA : A < 2 * r)
    (hv1 : ∀ i < r, 1 ≤ v i) (S : ℕ → Prop) [DecidablePred S]
    (hv : ∀ i < r, psum v i + (if S i then 1 else 0) = psum (NormGoal.chr r A) i)
    {k : ℕ} (hk0 : 0 < k) (hk : k < r) (hSk : S k) (hSk1 : ¬ S (k - 1)) :
    k * A % r < A % r := by
  have hr0 : 0 < r := by omega
  have hdiv : A / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hc := NormReduce.chr_eq (A := A) hr0 (k - 1)
  have hvk := hv1 (k - 1) (by omega)
  have e1 := hv k hk
  rw [if_pos hSk] at e1
  have e2 := hv (k - 1) (by omega)
  rw [if_neg hSk1] at e2
  have e3 := psum_succ v (k - 1)
  have e4 := psum_succ (NormGoal.chr r A) (k - 1)
  rw [Nat.sub_add_cancel hk0] at e3 e4
  rw [hdiv] at hc
  have hms := NormReduce.mod_succ (A := A) hr0 (k - 1)
  rw [Nat.sub_add_cancel hk0] at hms
  have := Nat.mod_lt ((k - 1) * A) hr0
  split_ifs at hc with h
  · rw [if_pos h] at hms; omega
  · omega

/-- **Two non-adjacent left flips, unconditional cycle form, no site conditions.**
No positive `T`-cycle point `m ≠ 1` (any `gcd(L, r)`, no size hypothesis) has a valuation word
whose partial sums are those of `chr r L` minus one at two distinct, non-adjacent sites in
`(0, r)`: the down-site conditions follow from validity (`down_site_of_valid`). -/
theorem cycle_two_left_flips_nonadj {m L r : ℕ} {v : ℕ → ℕ}
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hadj1 : k₁ + 1 ≠ k₂) (hadj2 : k₂ + 1 ≠ k₁)
    (hv : ∀ i < r, psum v i + (if i = k₁ ∨ i = k₂ then 1 else 0) = psum (NormGoal.chr r L) i) :
    False := by
  obtain ⟨hL2, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨hq, _⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  have hrL := NormReduce.r_lt_A hq
  have hs1 := down_site_of_valid (S := fun i => i = k₁ ∨ i = k₂) hrL hL2 hv1 hv h1 h1r
    (Or.inl rfl) (by omega)
  have hs2 := down_site_of_valid (S := fun i => i = k₁ ∨ i = k₂) hrL hL2 hv1 hv h2 h2r
    (Or.inr rfl) (by omega)
  exact cycle_two_left_flips_uncond hv1 hL hodd hcyc hm k₁ k₂ h1 h1r h2 h2r hne hs1 hs2 hv

/-- **`k` right flips, unconditional cycle form (coprime).** No positive `T`-cycle
point `m ≠ 1` with `gcd(L, r) = 1` has a valuation word obtained from `chr r L` by `+1`
partial-sum flips on a set `K` of at least two sites in `(0, r)` with
`Σ_{k∈K} 4^{p_k/r} ≤ 4.9` (`p_k = r - 1 - kL mod r`). No size or site hypotheses. -/
theorem cycle_k_right_flips_uncond {m L r : ℕ} {v : ℕ → ℕ} (hcop : Nat.Coprime L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (K : Finset ℕ) (hK2 : 2 ≤ K.card) (hKr : ∀ k ∈ K, 0 < k ∧ k < r)
    (hS : ∑ k ∈ K, (4:ℝ) ^ (((r - 1 - k * L % r : ℕ) : ℝ) / r) ≤ 49 / 10)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i ∈ K then 1 else 0)) : False := by
  have hr1 : 1 ≤ r := by
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < K.card by omega)
    have := hKr k hk; omega
  obtain ⟨hL2, hrb⟩ := cycle_params hr1 hv1 hL hodd hcyc hm
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_k_right_flips' r L (by omega) hcop hq K hK2 hKr hS v hv hdiv

/-- **Mixed up/down pair, unconditional cycle form (coprime).** `NormMixed`'s
`cycle_mixed_flips` with the hypothesis `r ≥ 2325` replaced by `m ≠ 1`. -/
theorem cycle_mixed_flips_uncond {m L r : ℕ} {v : ℕ → ℕ} (hcop : Nat.Coprime L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hm : m ≠ 1)
    (k k' : ℕ) (hk : 0 < k ∧ k < r) (hk' : 0 < k' ∧ k' < r)
    (hne : k ≠ k') (H1 : 2 ≤ k' * L % r) (H2 : k' * L % r + 3 ≤ k * L % r)
    (H3 : k * L % r + 3 ≤ r)
    (H4 : 5 * (4:ℝ) ^ (((k' * L % r + 1 : ℕ) : ℝ) / r) +
      6 * (4:ℝ) ^ (((r - k * L % r + k' * L % r : ℕ) : ℝ) / r) ≤ 289 / 10)
    (hv : ∀ i < r, (psum v i : ℤ) = psum (NormGoal.chr r L) i +
      (if i = k then 1 else 0) - (if i = k' then 1 else 0)) : False := by
  obtain ⟨hL2, hrb⟩ := cycle_params (by omega) hv1 hL hodd hcyc hm
  exact NormMixed.cycle_mixed_flips (by omega) hcop hv1 hL hodd hcyc k k' hk hk' hne H1 H2 H3 H4 hv

end Uncond

end CollatzSearch.NormCycleAll

#print axioms CollatzSearch.NormCycleAll.oddSteps_psum
#print axioms CollatzSearch.NormCycleAll.exists_odd_point
#print axioms CollatzSearch.NormCycleAll.cycle_params
#print axioms CollatzSearch.NormCycleAll.up_site_of_valid
#print axioms CollatzSearch.NormCycleAll.no_cycle_k_right_flips'
#print axioms CollatzSearch.NormCycleAll.cycle_two_right_flips_uncond
#print axioms CollatzSearch.NormCycleAll.cycle_two_right_flips_nonadj
#print axioms CollatzSearch.NormCycleAll.cycle_two_left_flips_uncond
#print axioms CollatzSearch.NormCycleAll.down_site_of_valid
#print axioms CollatzSearch.NormCycleAll.cycle_two_left_flips_nonadj
#print axioms CollatzSearch.NormCycleAll.cycle_k_right_flips_uncond
#print axioms CollatzSearch.NormCycleAll.cycle_mixed_flips_uncond
