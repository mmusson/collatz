import NormLevels
import Mathlib.Tactic.NormNum.Prime

/-!
# best-approximation plateau lift (every gcd) and a single-prime Lebel instance

Notation as in `NormShift`: `q = 2^A - 3^r`, `ε_j = A_j - ⌊jA/r⌋` (`eps`), cyclic arcs `arc`.

* `best_shift`: for `1 ≤ N < r/gcd(A,r)` a shift `σ ∈ {δ₀, r - δ₀}` (`δ₀ ≤ N` a best
  approximation of `0` by `δA mod r`) with `σA ≡ t (mod r)` whose special positions
  (`jA mod r < t`) are pairwise more than `N` apart cyclically.
* `plateau_word` (T1): ONE plateau (`ε` constant on an arc of length `≥ N + 2g + 1`) at bounded
  height already forces `q ∤ B(v)` once `2^{2h+174} r^59 < 3^{g+1}` (plus the cycle-equation
  gap). Every gcd; no coprimality.
* Corollaries: `window_word(_big)` (deviation confined to ANY arc of length `w` with
  `w + 3⌊r/60⌋ + 1 ≤ r`, i.e. about 95% of the circle at `r = 40901`; the first coprime window
  theorem, open since `NormCofactor`), `few_levels_plateau` (T5 with `|P|·3g < r`, i.e. `|P| ≤ 20` at
  `r = 40901`, `h ≤ 1`, vs `J ≤ 9` in `NormShift`), and the start-free `T`-cycle forms
  `cycle_plateau_rot`, `cycle_window_rot`, `cycle_few_levels_plateau`.
* `lebel_single_prime_37_19` (T2): at `(A, r) = (37, 19)`, `D = 5 · 27255338401`; `5` is bad
  for a one-move word, while `P^+(D)` divides `B` of no one-move word.
* `few_levels_gcd_nonvacuous` (non-vacuity of `NormLevels`), `window_witness`.

Credit: the `t = 1` lift is Mghirbi's (Zenodo 21734655, Thm 6.3/6.4, Lemma 7.2); the any-`t`,
any-gcd lift is `NormShift.shift_lift`; one-move framework: Knight, Lebel, Solomon.
Mghirbi's Thm 1.1 counts the defect support `s` and is vacuous once `s ≳ p / log p`; T1 needs
contiguity (one long plateau) instead, so the two are incomparable in general, and T1 is strictly
beyond it for arc supports of size `≫ r / log r`.

**De-novelty (cycle level).** At cycle level these statements are Terras-type 2-adic separation
plus the max bound: a bounded-height cycle cannot contain a Christoffel factor of length about
`3·60·log₂ r` (cf. `NormLevels.cycle_levels_max`). The new content is word level only
(rational cycles / the divisibility `q ∣ B`). No non-2-adic input was found.
-/

namespace Collatz.NormPlateauLift
open Collatz.NormGoal Collatz.NormReduce Collatz.NormShift Finset

/-- Reduction of `x < 2r` modulo `r`. -/
theorem mod2 {r x : ℕ} (hx : x < 2 * r) : x % r = if x < r then x else x - r := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A cyclic arc `[s, s+ℓ)` is the set of `(s + k) mod r`, `k < ℓ`. -/
theorem arc_iff {r s ℓ j : ℕ} (hs : s < r) (hℓ : ℓ ≤ r) (hj : j < r) :
    arc r s ℓ j ↔ ∃ k < ℓ, (s + k) % r = j := by
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · exact ⟨j - s, by omega, by rw [Nat.add_sub_cancel' h1, Nat.mod_eq_of_lt hj]⟩
    · refine ⟨j + r - s, by omega, ?_⟩
      rw [mod2 (x := s + (j + r - s)) (by omega)]; split_ifs <;> omega
  · rintro ⟨k, hk, rfl⟩
    rw [mod2 (x := s + k) (by omega)]; unfold arc; split_ifs <;> omega

/-- **Best-approximation shift.** Let `0 < r`, `1 ≤ N < r / gcd(A, r)`. Choose
`δ₀ ∈ [1, N]` minimising the distance `t` of `δ₀A` to `rℤ`, and `σ = δ₀` or `σ = r - δ₀` so that
`σA = rm + t`, `1 ≤ t < r`. Then special positions (`yA mod r < t`) are more than `N` apart:
if `y` is special and `1 ≤ k ≤ N`, then `y + k (mod r)` is not special. -/
theorem best_shift {r A N : ℕ} (hr : 0 < r) (hN1 : 1 ≤ N) (hN : N < r / Nat.gcd A r) :
    ∃ σ m t δ0, σ < r ∧ σ * A = r * m + t ∧ 1 ≤ t ∧ t < r ∧ 1 ≤ δ0 ∧ δ0 ≤ N ∧
      (σ = δ0 ∨ σ = r - δ0) ∧
      ∀ y, y * A % r < t → ∀ k, 1 ≤ k → k ≤ N → ¬ ((y + k) % r * A % r < t) := by
  obtain ⟨δ0, hδ0, hmin⟩ := (Finset.Icc 1 N).exists_min_image
    (fun δ => min (δ * A % r) (r - δ * A % r)) ⟨1, by simp [hN1]⟩
  rw [Finset.mem_Icc] at hδ0
  have hNr : N < r := lt_of_lt_of_le hN (Nat.div_le_self _ _)
  have hnz : δ0 * A % r ≠ 0 := by
    intro h0
    have hd0 : 0 < Nat.gcd A r := Nat.gcd_pos_of_pos_right _ hr
    have hdvd : r ∣ δ0 * A := Nat.dvd_of_mod_eq_zero h0
    have h1 : r / Nat.gcd A r ∣ δ0 * A / Nat.gcd A r :=
      Nat.div_dvd_div (Nat.gcd_dvd_right A r) hdvd
    rw [Nat.mul_div_assoc _ (Nat.gcd_dvd_left A r)] at h1
    have hcop : Nat.Coprime (r / Nat.gcd A r) (A / Nat.gcd A r) :=
      (Nat.coprime_div_gcd_div_gcd hd0).symm
    have h2 := hcop.dvd_of_dvd_mul_right h1
    have := Nat.le_of_dvd (by omega) h2
    omega
  have hlt0 : δ0 * A % r < r := Nat.mod_lt _ hr
  obtain ⟨t, ht⟩ : ∃ t, t = min (δ0 * A % r) (r - δ0 * A % r) := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by omega
  have htr : t < r := by omega
  have core : ∀ δ, 1 ≤ δ → δ ≤ N → ∀ a a', a < t → a' < t → (a + δ * A % r) % r = a' →
      False := by
    intro δ h1 h2 a a' ha ha' h
    have hm := hmin δ (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    have he : δ * A % r < r := Nat.mod_lt _ hr
    rw [mod2 (x := a + δ * A % r) (by omega)] at h
    split_ifs at h <;> omega
  have hsp : ∀ y, y * A % r < t → ∀ k, 1 ≤ k → k ≤ N → ¬ ((y + k) % r * A % r < t) := by
    intro y hy k hk1 hkN hk
    rw [← mod_mul_eq, Nat.add_mul, Nat.add_mod] at hk
    exact core k hk1 hkN _ _ hy hk rfl
  have hdm := Nat.div_add_mod (δ0 * A) r
  by_cases hc : δ0 * A % r ≤ r - δ0 * A % r
  · refine ⟨δ0, δ0 * A / r, t, δ0, by omega, by omega, ht1, htr, hδ0.1, hδ0.2, Or.inl rfl, hsp⟩
  · have hA0 : 0 < A := by
      rcases Nat.eq_zero_or_pos A with h | h
      · subst h; simp at hnz
      · exact h
    set q := δ0 * A / r with hqd
    have hlt : δ0 * A < r * A := Nat.mul_lt_mul_of_pos_right (by omega) hA0
    have hqA : q + 1 ≤ A := by
      have : r * q < r * A := by omega
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    have e1 : (r - δ0) * A + δ0 * A = r * A := by rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    have e2 : r * (A - q - 1) + r * (q + 1) = r * A := by
      rw [← Nat.mul_add, Nat.sub_sub, Nat.sub_add_cancel hqA]
    have e3 : r * (q + 1) = r * q + r := by ring
    refine ⟨r - δ0, A - q - 1, t, δ0, by omega, by omega, ht1, htr, hδ0.1, hδ0.2, Or.inr rfl, hsp⟩

/-- **T1: plateau theorem, every gcd (word level).** Let `3^r + 1 < 2^A`, letters
`≥ 1`, `psum v r = A`, `|ε| ≤ h`, and `ε` constant (`= c`) on a cyclic arc of length
`ℓ ≥ N + 2g + 1` with `1 ≤ g ≤ N < r / gcd(A, r)`. With the gap `2^A ≤ 2^172 r^58 q` and
`2^{2h+174} r^59 < 3^{g+1}`, `q ∤ B(v)`.
Proof: `best_shift` gives specials more than `N` apart; on the part of the plateau where `ρ` and
`ρ - σ` both lie on it (length `≥ 2g + 1`) there is a special-free window of length `g`, where
`κ = 0`; apply `NormShift.shift_lift`. Cycle-level content: Terras separation + max bound (see
the module docstring); new content is word level. -/
theorem plateau_word {r A h N g ℓ s : ℕ} {c : ℤ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (hs : s < r) (hℓ : ℓ ≤ r) (hpl : ∀ j < r, arc r s ℓ j → eps r A v j = c)
    (hg1 : 1 ≤ g) (hgN : g ≤ N) (hN : N < r / Nat.gcd A r) (hlen : N + 2 * g + 1 ≤ ℓ)
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (2 * h + 174) * r ^ 59 < 3 ^ (g + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hr : 0 < r := by omega
  have hNr : N < r := lt_of_lt_of_le hN (Nat.div_le_self _ _)
  obtain ⟨σ, m, t, δ0, hσr, hσ, ht1, htr, hδ1, hδN, hσδ, hsp⟩ := best_shift hr (by omega) hN
  have hpl' : ∀ k < ℓ, eps r A v ((s + k) % r) = c := fun k hk =>
    hpl _ (Nat.mod_lt _ hr) ((arc_iff hs hℓ (Nat.mod_lt _ hr)).mpr ⟨k, hk, rfl⟩)
  obtain ⟨b, hb⟩ : ∃ b, ∀ k ≤ 2 * g, eps r A v ((s + (b + k)) % r) = c ∧
      eps r A v (back r σ ((s + (b + k)) % r)) = c := by
    rcases hσδ with hσδ | hσδ
    · refine ⟨δ0, fun k hk => ⟨hpl' _ (by omega), ?_⟩⟩
      rw [← mod_sub hr hσr (by omega), show s + (δ0 + k) - σ = s + k by omega]
      exact hpl' _ (by omega)
    · refine ⟨0, fun k hk => ⟨hpl' _ (by omega), ?_⟩⟩
      rw [← Nat.add_mod_right (s + (0 + k)) r, ← mod_sub hr hσr (by omega),
        show s + (0 + k) + r - σ = s + (k + δ0) by omega]
      exact hpl' _ (by omega)
  have hgr : g ≤ r := by omega
  have quiet_of : ∀ k ≤ 2 * g, ¬ ((s + (b + k)) % r * A % r < t) →
      quiet r A t σ v ((s + (b + k)) % r) := by
    intro k hk hns
    obtain ⟨h1, h2⟩ := hb k hk
    unfold quiet NormShift.wt; rw [ite_eq_right_of_eq_false _ _ (eq_false hns), h1, h2, add_zero]
  have hrun : ∃ x < r, ∀ j < r, arc r x g j → quiet r A t σ v j := by
    by_cases hex : ∃ k0 < g, (s + (b + k0)) % r * A % r < t
    · obtain ⟨k0, hk0, hk0t⟩ := hex
      refine ⟨(s + (b + (k0 + 1))) % r, Nat.mod_lt _ hr, fun j hj hxj => ?_⟩
      obtain ⟨k', hk', rfl⟩ := (arc_iff (Nat.mod_lt _ hr) hgr hj).mp hxj
      rw [Nat.mod_add_mod, show s + (b + (k0 + 1)) + k' = s + (b + (k0 + 1 + k')) by ring]
      apply quiet_of _ (by omega)
      have := hsp _ hk0t (k' + 1) (by omega) (by omega)
      rwa [Nat.mod_add_mod, show s + (b + k0) + (k' + 1) = s + (b + (k0 + 1 + k')) by ring]
        at this
    · push Not at hex
      refine ⟨(s + (b + 0)) % r, Nat.mod_lt _ hr, fun j hj hxj => ?_⟩
      obtain ⟨k', hk', rfl⟩ := (arc_iff (Nat.mod_lt _ hr) hgr hj).mp hxj
      rw [Nat.mod_add_mod, show s + (b + 0) + k' = s + (b + k') by ring]
      exact quiet_of _ (by omega) (not_lt.mpr (hex k' hk'))
  have hlo : ∀ j < r, j * A / r + 1 ≤ (h + 1) + psum v j := fun j hj => by
    have := hdn j hj; omega
  have hhi : ∀ j < r, (h + 1) + psum v j ≤ j * A / r + (2 * h + 1) := fun j hj => by
    have := hup j hj; omega
  have hsz := size_ok (E := 2 * h + 1) (g := g) hr (by omega) (by omega) hgap
    (by rw [show 173 + (2 * h + 1) = 2 * h + 174 by ring]; exact hbig)
  exact shift_lift (σ := σ) (t := t) (H := h + 1) (E := 2 * h + 1) hq hv1 hA hσr hσ ht1 htr
    hlo hhi (by omega) hsz hrun

/-! ### Numerics -/

set_option exponentiation.threshold 5000 in
/-- `2^176 (60N)^59 < 3^N` for `N ≥ 682`. -/
theorem big60 : ∀ N, 682 ≤ N → 2 ^ 176 * (60 * N) ^ 59 < 3 ^ N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h1 : (L + 1) * 682 ≤ 683 * L := by omega
    have h2 : ((L + 1) * 682) ^ 59 ≤ (683 * L) ^ 59 := Nat.pow_le_pow_left h1 59
    have h3 : 683 ^ 59 ≤ 3 * 682 ^ 59 := by norm_num
    have h4 : (L + 1) ^ 59 ≤ 3 * L ^ 59 := by
      rw [mul_pow, mul_pow] at h2
      have hp : 0 < 682 ^ 59 := by positivity
      have : (L + 1) ^ 59 * 682 ^ 59 ≤ 3 * L ^ 59 * 682 ^ 59 := by
        calc (L + 1) ^ 59 * 682 ^ 59 ≤ 683 ^ 59 * L ^ 59 := h2
          _ ≤ (3 * 682 ^ 59) * L ^ 59 := Nat.mul_le_mul_right _ h3
          _ = 3 * L ^ 59 * 682 ^ 59 := by ring
      exact Nat.le_of_mul_le_mul_right this hp
    calc 2 ^ 176 * (60 * (L + 1)) ^ 59 = 60 ^ 59 * (2 ^ 176 * (L + 1) ^ 59) := by ring
      _ ≤ 60 ^ 59 * (2 ^ 176 * (3 * L ^ 59)) := by gcongr
      _ = 3 * (2 ^ 176 * (60 * L) ^ 59) := by ring
      _ < 3 * 3 ^ L := by omega
      _ = 3 ^ (L + 1) := by ring

/-- `2^176 r^59 < 3^{⌊r/60⌋+1}` for `r ≥ 40901`. -/
theorem big_r60 {r : ℕ} (hr : 40901 ≤ r) : 2 ^ 176 * r ^ 59 < 3 ^ (r / 60 + 1) := by
  have h := big60 (r / 60 + 1) (by omega)
  calc 2 ^ 176 * r ^ 59 ≤ 2 ^ 176 * (60 * (r / 60 + 1)) ^ 59 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ < _ := h

/-- Size bound at height `h ≤ 1`, `g = ⌊r/60⌋`, `r ≥ 40901`. -/
theorem hbig_of_le1 {r h : ℕ} (hr : 40901 ≤ r) (hh : h ≤ 1) :
    2 ^ (2 * h + 174) * r ^ 59 < 3 ^ (r / 60 + 1) :=
  lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (big_r60 hr)

/-- `⌊r/60⌋ < ⌊r/d⌋` for `0 < d < 60`, `r ≥ 40901`. -/
theorem N60_lt {r d : ℕ} (hr : 40901 ≤ r) (hd0 : 0 < d) (hd : d < 60) : r / 60 < r / d :=
  lt_of_lt_of_le (by omega : r / 60 < r / 59) (Nat.div_le_div_left (by omega) hd0)

/-! ### Corollary (a): windows -/

/-- **Corollary (a): window theorem.** If `ε_j = 0` outside a cyclic arc `[s, s+w)`, the
height is `≤ h`, and `r - w ≥ N + 2g + 1` (with the T1 size hypotheses), then `q ∤ B(v)`. -/
theorem window_word {r A h N g w s : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (hs : s < r) (hw : w ≤ r) (hout : ∀ j < r, ¬ arc r s w j → eps r A v j = 0)
    (hg1 : 1 ≤ g) (hgN : g ≤ N) (hN : N < r / Nat.gcd A r) (hlen : N + 2 * g + 1 ≤ r - w)
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (2 * h + 174) * r ^ 59 < 3 ^ (g + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hr : 0 < r := by omega
  refine plateau_word (s := (s + w) % r) (ℓ := r - w) (c := 0) hq hv1 hA hup hdn
    (Nat.mod_lt _ hr) (by omega) ?_ hg1 hgN hN hlen hgap hbig
  intro j hj hj'
  apply hout j hj
  intro hin
  obtain ⟨k, hk, hkj⟩ := (arc_iff (Nat.mod_lt _ hr) (by omega) hj).mp hj'
  obtain ⟨k2, hk2, hk2j⟩ := (arc_iff hs hw hj).mp hin
  rw [Nat.mod_add_mod, ← hk2j, mod2 (x := s + w + k) (by omega),
    mod2 (x := s + k2) (by omega)] at hkj
  split_ifs at hkj <;> omega

/-- Explicit window form: `r ≥ 40901`, height `≤ 1`, `gcd(A,r) < 60`. -/
theorem window_word_big {r A h w s : ℕ} {v : ℕ → ℕ} (hr : 40901 ≤ r) (hd : Nat.gcd A r < 60)
    (hh : h ≤ 1) (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (hs : s < r) (hout : ∀ j < r, ¬ arc r s w j → eps r A v j = 0)
    (hw : w + 3 * (r / 60) + 1 ≤ r) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v :=
  window_word (N := r / 60) (g := r / 60) hq hv1 hA hup hdn hs (by omega) hout (by omega) le_rfl
    (N60_lt hr (Nat.gcd_pos_of_pos_right _ (by omega)) hd) (by omega)
    (gap_all59 (by omega) (by omega)) (hbig_of_le1 hr hh)

/-! ### Corollary (b): few level changes, constant 3 -/

/-- `prv r ((y+1) mod r) = y mod r`. -/
theorem prv_succ_mod {r y : ℕ} (hr : 0 < r) : prv r ((y + 1) % r) = y % r := by
  have h1 := Nat.mod_lt y hr
  rw [← Nat.mod_add_mod, mod2 (x := y % r + 1) (by omega)]
  unfold prv
  split_ifs <;> first | contradiction | omega

/-- **Corollary (b): T5 with constant 3, every gcd.** If `ε` changes level (cyclically) only at
points of `P`, `|P| · 3g < r`, `3g + 1 ≤ r`, `1 ≤ g < r / gcd(A, r)`, height `≤ h` and the size
hypotheses hold, then `q ∤ B(v)`. (At `r = 40901`, `h ≤ 1`, `g = 681`: `|P| ≤ 20`.) -/
theorem few_levels_plateau {r A h g : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r A v c ≠ eps r A v (prv r c) → c ∈ P)
    (hg1 : 1 ≤ g) (hN : g < r / Nat.gcd A r) (hcount : P.card * (3 * g) < r) (h3g : 3 * g + 1 ≤ r)
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (2 * h + 174) * r ^ 59 < 3 ^ (g + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hr : 0 < r := by omega
  obtain ⟨x0, hx0, hfree⟩ := NormLebel.free_points (g := 3 * g) P hP (by omega) hcount
  set s := prv r x0 with hsd
  have hsr : s < r := by rw [hsd]; unfold prv; split_ifs <;> omega
  have hshift : ∀ k, (s + (k + 1)) % r = (x0 + k) % r := by
    intro k; rw [hsd]; unfold prv; split_ifs with h0
    · rw [show r - 1 + (k + 1) = (x0 + k) + r by omega, Nat.add_mod_right]
    · congr 1; omega
  have hconst : ∀ k ≤ 3 * g, eps r A v ((s + k) % r) = eps r A v s := by
    intro k hk
    induction k with
    | zero => rw [add_zero, Nat.mod_eq_of_lt hsr]
    | succ k ih =>
      rw [← ih (by omega)]
      have hin : arc r x0 (3 * g) ((s + (k + 1)) % r) :=
        (arc_iff hx0 (by omega) (Nat.mod_lt _ hr)).mpr ⟨k, by omega, (hshift k).symm⟩
      have hnot := hfree _ (Nat.mod_lt _ hr) hin
      by_contra hne
      apply hnot
      apply hchg _ (Nat.mod_lt _ hr)
      rwa [← add_assoc, prv_succ_mod hr]
  refine plateau_word (N := g) (s := s) (ℓ := 3 * g + 1) (c := eps r A v s) hq hv1 hA hup hdn
    hsr h3g ?_ hg1 le_rfl hN (by omega) hgap hbig
  intro j hj hj'
  obtain ⟨k, hk, rfl⟩ := (arc_iff hsr h3g hj).mp hj'
  exact hconst k (by omega)

/-! ### Corollary (c): start-free cycle forms -/

section Cycle
open CollatzProof

/-- Rotations of a cycle word keep letters, total and the cycle divisibility. -/
theorem rot_facts {r L k : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hv1 : ∀ i < r, 1 ≤ v i)
    (hL : psum v r = L) (hq : 3 ^ r + 1 < 2 ^ L) (hdiv : (2 ^ L - 3 ^ r) ∣ Bnum r v) :
    (∀ i < r, 1 ≤ NormLebel.rot r k v i) ∧ psum (NormLebel.rot r k v) r = L ∧
      (2 ^ L - 3 ^ r) ∣ Bnum r (NormLebel.rot r k v) := by
  refine ⟨fun i _ => hv1 _ (Nat.mod_lt _ (by omega)), ?_, ?_⟩
  · have h1 := NormLebel.Pe_rot (r := r) (k := k) (v := v) r
    have h2 := Pe_add hL k
    omega
  · exact (NormLebel.dvd_Bnum_rot (k := k) (by omega) hq dvd_rfl hL).mpr hdiv

/-- **Corollary (c): start-free cycle form of T1.** No positive `T`-cycle (`r ≥ 2` odd steps,
period `L`) has a valuation word, read from ANY start `k`, of height `≤ h` against `chr r L`
with a plateau of length `≥ N + 2g + 1`, `1 ≤ g ≤ N < r / gcd(L, r)`,
`2^{2h+174} r^59 < 3^{g+1}`. (The trivial cycle is excluded automatically: there `r/gcd = 1`.)
Cycle level: Terras + max bound, see the module docstring. -/
theorem cycle_plateau_rot {m L r k h N g ℓ s : ℕ} {c : ℤ} {v : ℕ → ℕ} (hr : 2 ≤ r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hup : ∀ j < r, psum (NormLebel.rot r k v) j ≤ j * L / r + h)
    (hdn : ∀ j < r, j * L / r ≤ psum (NormLebel.rot r k v) j + h)
    (hs : s < r) (hℓ : ℓ ≤ r)
    (hpl : ∀ j < r, arc r s ℓ j → eps r L (NormLebel.rot r k v) j = c)
    (hg1 : 1 ≤ g) (hgN : g ≤ N) (hN : N < r / Nat.gcd L r) (hlen : N + 2 * g + 1 ≤ ℓ)
    (hbig : 2 ^ (2 * h + 174) * r ^ 59 < 3 ^ (g + 1)) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨h1, h2, h3⟩ := rot_facts (k := k) hr hv1 hL hq hdiv
  exact plateau_word hq h1 h2 hup hdn hs hℓ hpl hg1 hgN hN hlen
    (gap_all59 (by omega) (by omega)) hbig h3

/-- Start-free window form: no nontrivial positive `T`-cycle with `gcd(L, r) < 60` has a word
(any start) of height `≤ 1` whose deviation from `chr r L` lies in an arc of length `w` with
`w + 3⌊r/60⌋ + 1 ≤ r`. -/
theorem cycle_window_rot {m L r k h w s : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hm : m ≠ 1)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hd : Nat.gcd L r < 60) (hh : h ≤ 1)
    (hup : ∀ j < r, psum (NormLebel.rot r k v) j ≤ j * L / r + h)
    (hdn : ∀ j < r, j * L / r ≤ psum (NormLebel.rot r k v) j + h)
    (hs : s < r) (hout : ∀ j < r, ¬ arc r s w j → eps r L (NormLebel.rot r k v) j = 0)
    (hw : w + 3 * (r / 60) + 1 ≤ r) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨-, hr4⟩ := NormCycleAll.cycle_params (by omega) hv1 hL hodd hcyc hm
  obtain ⟨h1, h2, h3⟩ := rot_facts (k := k) hr hv1 hL hq hdiv
  exact window_word_big hr4 hd hh hq h1 h2 hup hdn hs hout hw h3

/-- Start-free form of corollary (b) for `T`-cycles. -/
theorem cycle_few_levels_plateau {m L r k h g : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hup : ∀ j < r, psum (NormLebel.rot r k v) j ≤ j * L / r + h)
    (hdn : ∀ j < r, j * L / r ≤ psum (NormLebel.rot r k v) j + h)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r L (NormLebel.rot r k v) c ≠
        eps r L (NormLebel.rot r k v) (prv r c) → c ∈ P)
    (hg1 : 1 ≤ g) (hN : g < r / Nat.gcd L r) (hcount : P.card * (3 * g) < r)
    (h3g : 3 * g + 1 ≤ r) (hbig : 2 ^ (2 * h + 174) * r ^ 59 < 3 ^ (g + 1)) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨h1, h2, h3⟩ := rot_facts (k := k) hr hv1 hL hq hdiv
  exact few_levels_plateau hq h1 h2 hup hdn P hP hchg hg1 hN hcount h3g
    (gap_all59 (by omega) (by omega)) hbig h3

end Cycle

/-! ### Non-vacuity -/

/-- Christoffel letters are `≥ 1` when `r ≤ A`. -/
theorem chr_ge_one {r A : ℕ} (hr : 0 < r) (hAr : r ≤ A) (i : ℕ) : 1 ≤ NormGoal.chr r A i := by
  have : i * A / r + 1 ≤ (i + 1) * A / r := by
    rw [← Nat.add_div_right _ hr]; apply Nat.div_le_div_right; nlinarith
  unfold NormGoal.chr; omega

/-- `ε ≡ 0` for the Christoffel word. -/
theorem eps_chr {r A : ℕ} (j : ℕ) : eps r A (NormGoal.chr r A) j = 0 := by
  unfold eps; rw [psum_chr]; simp

set_option maxRecDepth 100000 in
/-- **Witness for the window theorem (coprime case).** `(A, r) = (64830, 40903)` is coprime,
`3^r + 1 < 2^A`, and `2^176 r^59 < 3^{⌊r/60⌋+1}`; the Christoffel word `chr` itself meets every
hypothesis of `window_word_big` (with `w = 0`), so the hypotheses are jointly satisfiable. -/
theorem window_witness : Nat.Coprime 64830 40903 ∧ 3 ^ 40903 + 1 < 2 ^ 64830 ∧
    2 ^ 176 * 40903 ^ 59 < 3 ^ (40903 / 60 + 1) ∧
    ¬ (2 ^ 64830 - 3 ^ 40903) ∣ Bnum 40903 (NormGoal.chr 40903 64830) := by
  have hq : 3 ^ 40903 + 1 < 2 ^ 64830 := by decide +kernel
  have hc : Nat.gcd 64830 40903 = 1 := by decide +kernel
  refine ⟨hc, hq, by decide +kernel, ?_⟩
  refine window_word_big (h := 0) (w := 0) (s := 0) (by norm_num)
    (by rw [hc]; norm_num) (by norm_num) hq (fun i _ => chr_ge_one (by norm_num) (by norm_num) i)
    (by rw [psum_chr, Nat.mul_div_cancel_left _ (by norm_num)])
    (fun j _ => by rw [psum_chr]; omega) (fun j _ => by rw [psum_chr]; omega) (by norm_num)
    (fun j _ _ => eps_chr j) (by norm_num)

set_option maxRecDepth 100000 in
/-- **Non-vacuity of `NormLevels.few_levels_gcd` at `d = 2`.** For `v = NormGoal.chr 40902 64832`,
`P = ∅`, `H₀ = 0`, every hypothesis of `NormLevels.few_levels_gcd` holds
(here `g = ⌊40902/6⌋ = 6817`). -/
theorem few_levels_gcd_nonvacuous :
    Nat.gcd 64832 40902 = 2 ∧ 2 ≤ 40902 / 2 ∧ 3 ^ 40902 + 1 < 2 ^ 64832 ∧
    (∀ i < 40902, 1 ≤ NormGoal.chr 40902 64832 i) ∧ psum (NormGoal.chr 40902 64832) 40902 = 64832 ∧
    (∀ c < 40902, eps 40902 64832 (NormGoal.chr 40902 64832) c ≠
        eps 40902 64832 (NormGoal.chr 40902 64832) (prv 40902 c) → c ∈ (∅ : Finset ℕ)) ∧
    (∀ j < 40902, psum (NormGoal.chr 40902 64832) j ≤ j * 64832 / 40902 + 0) ∧
    (∀ j < 40902, j * 64832 / 40902 ≤ psum (NormGoal.chr 40902 64832) j + 0) ∧
    2 ^ 64832 ≤ 2 ^ 172 * 40902 ^ 58 * (2 ^ 64832 - 3 ^ 40902) ∧
    2 ^ (2 * 0 + 174) * 40902 ^ 59 <
      3 ^ (40902 / ((6 * (∅ : Finset ℕ).card + 3) * 2) + 1) := by
  have hq : 3 ^ 40902 + 1 < 2 ^ 64832 := by decide +kernel
  refine ⟨by decide +kernel, by norm_num, hq,
    fun i _ => chr_ge_one (by norm_num) (by norm_num) i,
    by rw [psum_chr, Nat.mul_div_cancel_left _ (by norm_num)],
    fun c _ h => absurd (by rw [eps_chr, eps_chr]) h,
    fun j _ => by rw [psum_chr]; omega, fun j _ => by rw [psum_chr]; omega,
    gap_all59 (by norm_num) (by omega), ?_⟩
  rw [Finset.card_empty]
  decide +kernel

/-! ### T2: a single-prime instance of Lebel's Conjecture 11.1 with composite `D` -/

set_option maxRecDepth 200000 in
/-- `27255338401` is prime (`norm_num` trial division). -/
theorem prime_27255338401 : Nat.Prime 27255338401 := by norm_num

/-- **Lebel Conj. 11.1, strong form, at `(A, r) = (37, 19)`.**
`D = 2^37 - 3^19 = 5 · 27255338401` with `P = 27255338401` prime, so `P = P^+(D)`. The prime `5`
is BAD: it divides `B` of the one-move word `slide (NormGoal.chr 19 37) 4 5` (cf. Lebel's Thm 7.2).
Yet `P` divides `B` of NO one-move neighbour of `NormGoal.chr 19 37` (`NormLebel.lebel_strong_of_large_prime`,
size margin about 600.7 vs 658.7 bits). An instance only; the conjecture stays open. -/
theorem lebel_single_prime_37_19 :
    2 ^ 37 - 3 ^ 19 = 5 * 27255338401 ∧ Nat.Prime 27255338401 ∧
    (∃ v, OneMove 19 (NormGoal.chr 19 37) v ∧ 5 ∣ Bnum 19 v) ∧
    (∀ p, p.Prime → p ∣ 2 ^ 37 - 3 ^ 19 → p ≤ 27255338401) ∧
    ∀ v, OneMove 19 (NormGoal.chr 19 37) v → ¬ 27255338401 ∣ Bnum 19 v := by
  have hD : 2 ^ 37 - 3 ^ 19 = 5 * 27255338401 := by norm_num
  have hmax : ∀ p, p.Prime → p ∣ 2 ^ 37 - 3 ^ 19 → p ≤ 27255338401 := by
    intro p hp hpD
    rw [hD] at hpD
    rcases (Nat.Prime.dvd_mul hp).mp hpD with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact Nat.le_of_dvd (by norm_num) h
  have hPD : 27255338401 ∣ 2 ^ 37 - 3 ^ 19 := by rw [hD]; exact Dvd.intro_left _ rfl
  refine ⟨hD, prime_27255338401, ⟨slide (NormGoal.chr 19 37) 4 5, ?_, by decide +kernel⟩, hmax, ?_⟩
  · exact Or.inr ⟨4, by norm_num, by decide, 5, Or.inl (by norm_num), by norm_num, by norm_num, rfl⟩
  · exact NormLebel.lebel_strong_of_large_prime 19 37 27255338401 27255338401 (by norm_num)
      (by norm_num) (by norm_num) prime_27255338401 hPD (by decide +kernel) hPD hmax

end Collatz.NormPlateauLift

#print axioms Collatz.NormPlateauLift.best_shift
#print axioms Collatz.NormPlateauLift.plateau_word
#print axioms Collatz.NormPlateauLift.big_r60
#print axioms Collatz.NormPlateauLift.window_word
#print axioms Collatz.NormPlateauLift.window_word_big
#print axioms Collatz.NormPlateauLift.few_levels_plateau
#print axioms Collatz.NormPlateauLift.cycle_plateau_rot
#print axioms Collatz.NormPlateauLift.cycle_window_rot
#print axioms Collatz.NormPlateauLift.cycle_few_levels_plateau
#print axioms Collatz.NormPlateauLift.window_witness
#print axioms Collatz.NormPlateauLift.few_levels_gcd_nonvacuous
#print axioms Collatz.NormPlateauLift.prime_27255338401
#print axioms Collatz.NormPlateauLift.lebel_single_prime_37_19
