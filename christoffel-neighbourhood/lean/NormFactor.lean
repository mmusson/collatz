import NormPlateauLift

/-!
# the lift as a factor-complexity theorem; Christoffel pieces of any slope

Notation as in `NormShift`: `v` a valuation word of length `r` (letters `≥ 1`, total `A`),
`q = 2^A - 3^r`, `B(v) = Bnum r v`, height `≤ h` means `|psum v j - ⌊jA/r⌋| ≤ h` for `j < r`.

* `rep_factor` (T1, repeated-factor theorem, any `gcd(A, r)`): if two cyclic factors of `v` of
  length `g` coincide at a cyclic distance `σ` with `1 ≤ σ < r / gcd(A, r)`, the height is `≤ h`
  and the size hypothesis holds (`E = 6h + 2`), then `q ∤ B(v)`. Equivalently: for a bounded
  height word with `q ∣ B(v)`, the `r` cyclic factors of length `g ≈ 0.63(6h + 181 + 59 log₂ r)`
  are pairwise distinct at every distance `< r/gcd`; in the coprime case the length-`g` factor
  complexity is maximal (`= r`). `rep_factor_gap`: same with the cycle-equation gap
  `2^A ≤ 2^172 r^58 q` and `2^{175+6h} r^59 < 3^{g+1}`.
  Proof: the quiet run of `NormShift.lift_core` (`Pe(i) = m + Pe(i - σ)`) is exactly a repeated
  factor; `σ, m` are arbitrary, the slope only enters the exponent bounds; a non-quiet point
  exists because otherwise `σA = rm`, forcing `r/gcd ∣ σ`.
* `chr_rep`: every factor of length `≥ N + 2g + 3` of a Christoffel word `chr s p` of ANY slope
  (`g + 1 ≤ N`) contains a repeated factor of length `g` at distance `δ ∈ [1, N]`
  (periodic case `s/gcd(p,s) ≤ N`, else best approximation shift `NormPlateauLift.best_shift`).
* `chr_piece` (T2): a bounded-height `v` agreeing on an arc of length `≥ N + 2g + 3` with a
  factor of `chr s p` (any `s ≥ 1`, any `p`), `g + 1 ≤ N < r/gcd(A, r)`: `q ∤ B(v)`.
* `chr_pieces` (T2b, K-piece theorem): if every cyclic arc of length `ℓ` that avoids a cut set `P`
  agrees with a factor of some Christoffel word (slopes may vary from arc to arc) and
  `|P| · ℓ < r`, then `q ∤ B(v)`. (The real content is
  `chr_piece` — ONE Christoffel factor of length `ℓ ≈ 3g` suffices; `|P| · ℓ < r` is only the
  pigeonhole that supplies such an arc, which is where the piece count comes from.) So a bounded-height word with `q ∣ B(v)` needs about
  `r / (3g)` balanced pieces. This contains `NormMain`/`NormAll` (one move), `NormShift` (slides), `NormLevels` (few
  levels) and `NormPlateauLift` (plateaus, windows) for large `r`, and also bounded-height words with `Θ(r)`
  level changes, e.g. `chr(r₁, A₁+1) chr(r₂, A₂-1)`, which `NormShift`'s T5 cannot reach.
* `big_r50`, `cycle_chr_pieces_rot`, `cycle_chr_pieces_big`: start-free `T`-cycle forms.
* `chr_piece_witness` (non-vacuity): all hypotheses of `chr_piece` (hence of `rep_factor_gap`)
  hold at `v = slide (chr 40903 64830) 1 20001`, `h = 1`, a word with deviation `-1` on the
  whole arc used.

**Limit of the lift family.** Every lift (the earlier files) needs a repeated factor of length
`≈ c(h + log r)` at distance `< r/gcd`; words whose factor complexity is maximal at that scale
(exponentially many) are untouched by any lift.

**Scope / de-novelty (mandatory).** Word level: new in form (factor-complexity phrasing; pieces
of arbitrary slopes). **Cycle level = Terras + max bound**: two odd cycle elements followed by
the same valuation factor `u` are congruent mod `2^{|u|₁+1}` (Terras/Everett 2-adic
separation), so the cycle maximum is `≳ 2^{1.58 g}`, while height `≤ h` and the minimum bound
`m ≤ 2^171 L^59` bound it above (`NormLevels` `cycle_levels_max`). Real cycles are not known to have
bounded height, so nothing is excluded unconditionally.

**Scope notes.** (1) The arbitrary-slope feature is UNWITNESSED at word level: the only
non-vacuity witness (`chr_piece_witness`) uses a piece of the word's own slope `r/A`. At the
cycle level the arbitrary-slope statements are unconditional and need no witness:
`CycleMech.cycle_mech_pieces_ratio` / `CycleMech.finite_ratio_mech_pieces` (bounded ratio,
`K` mechanical pieces) and `CycleMech.cycle_no_mech_arc_frac` (no mechanical arc of any slope of
length `⌈4L/5⌉`, no height hypothesis). (2) Every bounded-height norm result of the earlier files
(`NormLevels`, `NormFactor`, ...) follows, for large `r`, from Terras (`modEq_of_parity`) plus
`min_le_poly_period59` via Böhm–Sontacchi: `q ∣ B(v)` gives an integer cycle, bounded height
gives max `≤ 2^{h+O(1)}` min, and two points with the same parity window of length `g` coincide
once `2^g >` max.

Credit: Mghirbi (Zenodo 21734655: the `t = 1` rotation-numerator lift), Knight, Lebel,
Solomon (one-move framework), Fernández–Ibáñez arXiv 2607.24844; `NormShift` `NormShift.shift_lift`.
-/

namespace Collatz.NormFactor
open Collatz.NormGoal Collatz.NormReduce Collatz.NormShift Finset

/-! ### T1: repeated factor -/

/-- **T1: repeated-factor theorem, any gcd (word level).** Let `3^r + 1 < 2^A`,
letters `≥ 1` below `r`, `psum v r = A`, height `≤ h` about `chr r A`. If the cyclic factors of
length `g < r` starting at `x` and at `x + σ` coincide, with `1 ≤ σ < r / gcd(A, r)`, and
`(r 2^{6h+2})^r 2^{A(r-1-g)+r} < q^r`, then `q ∤ B(v)`. Cycle level: Terras + max bound. -/
theorem rep_factor {r A h g x σ : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (hσ1 : 1 ≤ σ) (hσ : σ < r / Nat.gcd A r) (hg : g < r)
    (hrep : ∀ k < g, v ((x + σ + k) % r) = v ((x + k) % r))
    (hsz : (r * 2 ^ (6 * h + 2)) ^ r * 2 ^ (A * (r - 1 - g) + r) < (2 ^ A - 3 ^ r) ^ r) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdvd
  have hr : 0 < r := by omega
  -- heights for all i
  have hup' : ∀ i, Pe r v i ≤ i * A / r + h := by
    intro i; have := hup (i % r) (Nat.mod_lt _ hr); rw [Pe_mod hr hA, c_mod hr]; omega
  have hdn' : ∀ i, i * A / r ≤ Pe r v i + h := by
    intro i; have := hdn (i % r) (Nat.mod_lt _ hr); rw [Pe_mod hr hA, c_mod hr]; omega
  -- floor shift by σ
  set F := σ * A / r with hF
  have hσA : σ * A = r * F + σ * A % r := (Nat.div_add_mod _ _).symm
  have hfl : ∀ i, σ ≤ i → i * A / r ≤ (i - σ) * A / r + F + 1 ∧
      (i - σ) * A / r + F ≤ i * A / r := by
    intro i hi
    have := floor_shift hr hσA (Nat.mod_lt _ hr) hi; split_ifs at this <;> omega
  -- shift increment
  set m := Pe r v (x + σ) - Pe r v x with hm
  have hmono := Pe_mono hr hv1 x σ
  have hrun : ∀ k ≤ g, Pe r v (x + σ + k) = m + Pe r v (x + k) := by
    intro k hk
    induction k with
    | zero => simp only [add_zero]; omega
    | succ k ih =>
      rw [← add_assoc, ← add_assoc, Pe_succ, Pe_succ, ih (by omega), hrep k (by omega)]; ring
  have hmb : F ≤ m + 2 * h ∧ m ≤ F + 1 + 2 * h := by
    have h1 := hup' (x + σ); have h2 := hdn' x; have h3 := hup' x; have h4 := hdn' (x + σ)
    have h5 := hfl (x + σ) (by omega)
    rw [Nat.add_sub_cancel] at h5
    omega
  -- quietness
  let Q : ℕ → Prop := fun i => Pe r v i = m + Pe r v (i - σ)
  have hper : ∀ i, σ ≤ i → (Q (i + r) ↔ Q i) := by
    intro i hi
    show Pe r v (i + r) = m + Pe r v (i + r - σ) ↔ Pe r v i = m + Pe r v (i - σ)
    rw [show i + r - σ = (i - σ) + r by omega, Pe_add hA, Pe_add hA]
    constructor <;> intro h <;> omega
  have hperm : ∀ i n, σ ≤ i → (Q (i + r * n) ↔ Q i) := by
    intro i n hi
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show i + r * (n + 1) = (i + r * n) + r by ring, hper _ (by omega), ih]
  -- a non-quiet point exists
  have hne : ∃ i, σ ≤ i ∧ ¬ Q i := by
    by_contra hcon; push Not at hcon
    have hit : ∀ n, Pe r v (n * σ) = n * m := by
      intro n; induction n with
      | zero => simp [Pe_zero]
      | succ n ih =>
        have := hcon ((n + 1) * σ) (Nat.le_mul_of_pos_left σ (by omega))
        simp only [Q] at this
        rw [show (n + 1) * σ - σ = n * σ by rw [add_mul, one_mul, Nat.add_sub_cancel], ih] at this
        rw [this]; ring
    have h1 := hit r
    have h2 := Pe_add_mul hA 0 σ
    rw [zero_add, Pe_zero, zero_add] at h2
    rw [h1] at h2
    -- σ * A = r * m
    have hd0 : 0 < Nat.gcd A r := Nat.gcd_pos_of_pos_right _ hr
    have hdvd' : r ∣ σ * A := ⟨m, by rw [mul_comm σ A]; omega⟩
    have h1' : r / Nat.gcd A r ∣ σ * A / Nat.gcd A r :=
      Nat.div_dvd_div (Nat.gcd_dvd_right A r) hdvd'
    rw [Nat.mul_div_assoc _ (Nat.gcd_dvd_left A r)] at h1'
    have hcop : Nat.Coprime (r / Nat.gcd A r) (A / Nat.gcd A r) :=
      (Nat.coprime_div_gcd_div_gcd hd0).symm
    have h2' := hcop.dvd_of_dvd_mul_right h1'
    have := Nat.le_of_dvd (by omega) h2'
    omega
  -- first non-quiet point after the run
  set B0 := x + σ + g + 1 with hB0
  have hex : ∃ j, ¬ Q (B0 + j) := by
    obtain ⟨i0, hi0, hq0⟩ := hne
    refine ⟨i0 + r * B0 - B0, ?_⟩
    have : B0 ≤ r * B0 := Nat.le_mul_of_pos_left _ hr
    rw [Nat.add_sub_cancel' (by omega), hperm _ _ hi0]; exact hq0
  classical
  have hj0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, Q (B0 + j) :=
    fun j hj => by have := Nat.find_min hex hj; push Not at this; exact this
  have hquiet : ∀ i, x + σ ≤ i → i < B0 + Nat.find hex → Q i := by
    intro i hi1 hi2
    by_cases hc : i ≤ x + σ + g
    · have := hrun (i - (x + σ)) (by omega)
      show Pe r v i = m + Pe r v (i - σ)
      rw [show x + σ + (i - (x + σ)) = i by omega, show x + (i - (x + σ)) = i - σ by omega] at this
      exact this
    · have := hmin (i - B0) (by omega)
      rwa [show B0 + (i - B0) = i by omega] at this
  apply lift_core (σ := σ) (m := m) (H := 3 * h + 1) (E := 6 * h + 2)
    (a := B0 + Nat.find hex) (T := r - 1 - g) hr hq hv1 hA hdvd (by omega) (by omega)
  · intro i _; have := hdn' i; omega
  · intro i hi; have := hdn' (i - σ); have := hfl i hi; omega
  · intro i _; have := hdn' i; have := hup' i; omega
  · intro i hi; have := hup' (i - σ); have := hfl i hi; omega
  · exact hj0
  · intro j hj1 hj2
    have hσ' : σ ≤ B0 + Nat.find hex + j - r := by omega
    have := (hper _ hσ').mpr (hquiet _ (by omega) (by omega))
    rwa [show B0 + Nat.find hex + j - r + r = B0 + Nat.find hex + j by omega] at this
  · exact hsz


/-- `rep_factor` with the cycle-equation gap `2^A ≤ 2^172 r^58 q` and
`2^{175+6h} r^59 < 3^{g+1}` in place of the raw size hypothesis. -/
theorem rep_factor_gap {r A h g x σ : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (hσ1 : 1 ≤ σ) (hσ : σ < r / Nat.gcd A r) (hg : g < r)
    (hrep : ∀ k < g, v ((x + σ + k) % r) = v ((x + k) % r))
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (175 + 6 * h) * r ^ 59 < 3 ^ (g + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v :=
  rep_factor hq hv1 hA hup hdn hσ1 hσ hg hrep
    (size_ok (by omega) (by omega) hg hgap (by rw [show 173 + (6 * h + 2) = 175 + 6 * h by ring]; exact hbig))

/-! ### Repeated factors inside Christoffel words of any slope -/

/-- `chr s p` is `s`-periodic. -/
theorem chr_period {s p : ℕ} (hs : 1 ≤ s) (z : ℕ) : NormGoal.chr s p (z + s) = NormGoal.chr s p z := by
  unfold NormGoal.chr
  rw [show (z + s + 1) * p = (z + 1) * p + s * p by ring,
    show (z + s) * p = z * p + s * p by ring,
    Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega)]
  omega

/-- `chr s p` has period `s / gcd(p, s)`. -/
theorem chr_period' {s p : ℕ} (hs : 1 ≤ s) (z : ℕ) :
    NormGoal.chr s p (z + s / Nat.gcd p s) = NormGoal.chr s p z := by
  obtain ⟨s', hs'⟩ := Nat.gcd_dvd_right p s
  obtain ⟨p', hp'⟩ := Nat.gcd_dvd_left p s
  have hd : 0 < Nat.gcd p s := Nat.gcd_pos_of_pos_right _ (by omega)
  set d := Nat.gcd p s
  have e : s / d = s' := by
    rw [hs']; exact Nat.mul_div_cancel_left _ hd
  rw [e]
  unfold NormGoal.chr
  have e1 : (z + s' + 1) * p = (z + 1) * p + s * p' := by
    rw [hs', hp']; ring
  have e2 : (z + s') * p = z * p + s * p' := by
    rw [hs', hp']; ring
  rw [e1, e2, Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega)]
  omega

/-- **Repeated factor inside a Christoffel word.** Any factor of length `ℓ ≥ N + 2g + 3` of
`NormGoal.chr s p` (any slope, `s ≥ 1`), with `g + 1 ≤ N`, contains two occurrences of one factor of
length `g` at a distance `δ ∈ [1, N]`. -/
theorem chr_rep {s p g N ℓ c : ℕ} (hs : 1 ≤ s) (hgN : g + 1 ≤ N) (hlen : N + 2 * g + 3 ≤ ℓ) :
    ∃ δ b, 1 ≤ δ ∧ δ ≤ N ∧ b + δ + g ≤ ℓ ∧
      ∀ k < g, NormGoal.chr s p (c + b + δ + k) = NormGoal.chr s p (c + b + k) := by
  by_cases hA : s / Nat.gcd p s ≤ N
  · have hd : 0 < Nat.gcd p s := Nat.gcd_pos_of_pos_right _ (by omega)
    have h1 : 1 ≤ s / Nat.gcd p s :=
      (Nat.one_le_div_iff hd).mpr (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right p s))
    refine ⟨s / Nat.gcd p s, 0, h1, hA, by omega, fun k _ => ?_⟩
    rw [show c + 0 + s / Nat.gcd p s + k = (c + k) + s / Nat.gcd p s by ring, chr_period' hs]
    rfl
  push Not at hA
  obtain ⟨σ, m, t, δ0, hσs, hσ, ht1, hts, hδ1, hδN, hor, hsep⟩ :=
    NormPlateauLift.best_shift (r := s) (A := p) (N := N) (by omega) (by omega) hA
  -- floor identity
  have hfi : ∀ z, ¬ ((z + σ) * p % s < t) → ¬ ((z + σ + 1) * p % s < t) →
      NormGoal.chr s p (z + σ) = NormGoal.chr s p z := by
    intro z h1 h2
    have f1 := floor_shift (r := s) (i := z + σ) (by omega) hσ hts (by omega)
    have f2 := floor_shift (r := s) (i := z + σ + 1) (by omega) hσ hts (by omega)
    rw [if_neg h1, Nat.add_sub_cancel] at f1
    rw [if_neg h2, show z + σ + 1 - σ = z + 1 by omega] at f2
    unfold NormGoal.chr
    rw [show z + σ + 1 = z + σ + 1 from rfl, f1, f2]
    omega
  -- special-free run
  have hrun : ∀ y0, ∃ u0, u0 ≤ g + 1 ∧ ∀ k ≤ g, ¬ ((y0 + u0 + k) * p % s < t) := by
    intro y0
    by_cases hc : ∃ u, u ≤ g ∧ (y0 + u) * p % s < t
    · obtain ⟨u, hu, hsu⟩ := hc
      refine ⟨u + 1, by omega, fun k hk => ?_⟩
      have := hsep (y0 + u) hsu (k + 1) (by omega) (by omega)
      rw [← mod_mul_eq] at this
      rwa [show y0 + (u + 1) + k = y0 + u + (k + 1) by ring]
    · push Not at hc
      refine ⟨0, by omega, fun k hk => ?_⟩
      have := hc k hk; rw [add_zero]; omega
  have hspec_per : ∀ z, (z + s) * p % s = z * p % s := by
    intro z; rw [add_mul, Nat.add_mul_mod_self_left]
  rcases hor with h | h
  · subst h
    obtain ⟨u0, hu0, hfree⟩ := hrun (c + σ)
    refine ⟨σ, u0, hδ1, hδN, by omega, fun k hk => ?_⟩
    have := hfi (c + u0 + k) (by
      have := hfree k (by omega); rwa [show c + σ + u0 + k = c + u0 + k + σ by ring] at this)
      (by have := hfree (k + 1) (by omega)
          rwa [show c + σ + u0 + (k + 1) = c + u0 + k + σ + 1 by ring] at this)
    rw [show c + u0 + σ + k = c + u0 + k + σ by ring]; exact this
  · obtain ⟨u0, hu0, hfree⟩ := hrun c
    refine ⟨δ0, u0, hδ1, hδN, by omega, fun k hk => ?_⟩
    have e : c + u0 + k + δ0 + σ = (c + u0 + k) + s := by
      have := Nat.div_le_self s (Nat.gcd p s); omega
    have := hfi (c + u0 + k + δ0) (by
      rw [e, hspec_per]; exact hfree k (by omega))
      (by rw [e, show c + u0 + k + s + 1 = (c + u0 + (k + 1)) + s by ring, hspec_per]
          exact hfree (k + 1) (by omega))
    rw [e, chr_period hs] at this
    rw [show c + u0 + δ0 + k = c + u0 + k + δ0 by ring]; exact this.symm


/-! ### T2: Christoffel pieces of any slope -/

/-- **T2: one long Christoffel factor of ANY slope.** A word of height `≤ h` about
`chr r A` (letters `≥ 1`, total `A`, `3^r + 1 < 2^A`) which agrees on a cyclic arc of length
`ℓ ≥ N + 2g + 3` with a factor of `chr s p` for some `s ≥ 1` and any `p`, where
`g + 1 ≤ N < r / gcd(A, r)`, satisfies `q ∤ B(v)` under the gap and
`2^{175+6h} r^59 < 3^{g+1}`. Cycle level: Terras + max bound. -/
theorem chr_piece {r A h g N ℓ x s p c : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (hs : 1 ≤ s) (hgN : g + 1 ≤ N) (hN : N < r / Nat.gcd A r)
    (hlen : N + 2 * g + 3 ≤ ℓ) (hℓ : ℓ ≤ r)
    (hagree : ∀ k < ℓ, v ((x + k) % r) = NormGoal.chr s p (c + k))
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (175 + 6 * h) * r ^ 59 < 3 ^ (g + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  obtain ⟨δ, b, hδ1, hδN, hb, hrep⟩ := chr_rep (p := p) (c := c) hs hgN hlen
  refine rep_factor_gap (x := x + b) (σ := δ) hq hv1 hA hup hdn hδ1 (by omega) (by omega)
    (fun k hk => ?_) hgap hbig
  have e1 := hagree (b + δ + k) (by omega)
  have e2 := hagree (b + k) (by omega)
  rw [show x + b + δ + k = x + (b + δ + k) by ring, e1, show x + b + k = x + (b + k) by ring, e2,
    show c + (b + δ + k) = c + b + δ + k by ring, show c + (b + k) = c + b + k by ring]
  exact hrep k hk

/-- **T2b: the K-piece theorem.** Let `P` be a set of cut points `< r` and suppose
that every cyclic arc `[x, x+ℓ)` containing no point of `P` agrees with a factor of SOME
Christoffel word `chr s p` (`s ≥ 1`; the slope `p/s` may depend on the arc). If
`|P| · ℓ < r`, `ℓ ≥ N + 2g + 3`, `g + 1 ≤ N < r / gcd(A, r)`, the height is `≤ h` and the size
hypotheses hold, then `q ∤ B(v)`. In particular a concatenation of fewer than `r/ℓ` factors of
Christoffel words of arbitrary slopes (cuts at the piece starts) of bounded height has
`q ∤ B(v)`. Cycle level: Terras + max bound. Restated: one Christoffel factor of length
`ℓ ≈ 3g` suffices (`chr_piece`); pigeonhole gives the piece count. Arbitrary slopes are
unwitnessed at word level; see `CycleMech` for the unconditional cycle-level form. -/
theorem chr_pieces {r A h g N ℓ : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hup : ∀ j < r, psum v j ≤ j * A / r + h) (hdn : ∀ j < r, j * A / r ≤ psum v j + h)
    (P : Finset ℕ) (hP : ∀ e ∈ P, e < r) (hcount : P.card * ℓ < r)
    (hpw : ∀ x < r, (∀ j < r, arc r x ℓ j → j ∉ P) →
      ∃ s p c, 1 ≤ s ∧ ∀ k < ℓ, v ((x + k) % r) = NormGoal.chr s p (c + k))
    (hgN : g + 1 ≤ N) (hN : N < r / Nat.gcd A r) (hlen : N + 2 * g + 3 ≤ ℓ) (hℓ : ℓ ≤ r)
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (175 + 6 * h) * r ^ 59 < 3 ^ (g + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  obtain ⟨x, hx, hfree⟩ := NormLebel.free_points P hP hℓ hcount
  obtain ⟨s, p, c, hs, hag⟩ := hpw x hx hfree
  exact chr_piece hq hv1 hA hup hdn hs hgN hN hlen hℓ hag hgap hbig

/-! ### Numerics -/

set_option exponentiation.threshold 5000 in
/-- `2^181 (50N)^59 < 3^N` for `N ≥ 818`. -/
theorem big50 : ∀ N, 818 ≤ N → 2 ^ 181 * (50 * N) ^ 59 < 3 ^ N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h1 : (L + 1) * 818 ≤ 819 * L := by omega
    have h2 : ((L + 1) * 818) ^ 59 ≤ (819 * L) ^ 59 := Nat.pow_le_pow_left h1 59
    have h3 : 819 ^ 59 ≤ 3 * 818 ^ 59 := by norm_num
    have h4 : (L + 1) ^ 59 ≤ 3 * L ^ 59 := by
      rw [mul_pow, mul_pow] at h2
      have hp : 0 < 818 ^ 59 := by positivity
      have : (L + 1) ^ 59 * 818 ^ 59 ≤ 3 * L ^ 59 * 818 ^ 59 := by
        calc (L + 1) ^ 59 * 818 ^ 59 ≤ 819 ^ 59 * L ^ 59 := h2
          _ ≤ (3 * 818 ^ 59) * L ^ 59 := Nat.mul_le_mul_right _ h3
          _ = 3 * L ^ 59 * 818 ^ 59 := by ring
      exact Nat.le_of_mul_le_mul_right this hp
    calc 2 ^ 181 * (50 * (L + 1)) ^ 59 = 50 ^ 59 * (2 ^ 181 * (L + 1) ^ 59) := by ring
      _ ≤ 50 ^ 59 * (2 ^ 181 * (3 * L ^ 59)) := by gcongr
      _ = 3 * (2 ^ 181 * (50 * L) ^ 59) := by ring
      _ < 3 * 3 ^ L := by omega
      _ = 3 ^ (L + 1) := by ring

/-- `2^181 r^59 < 3^{⌊r/50⌋+1}` for `r ≥ 40901`. -/
theorem big_r50 {r : ℕ} (hr : 40901 ≤ r) : 2 ^ 181 * r ^ 59 < 3 ^ (r / 50 + 1) := by
  have h := big50 (r / 50 + 1) (by omega)
  calc 2 ^ 181 * r ^ 59 ≤ 2 ^ 181 * (50 * (r / 50 + 1)) ^ 59 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ < _ := h

/-- Size bound at height `h ≤ 1`, `g = ⌊r/50⌋`, `r ≥ 40901`. -/
theorem hbig50_of_le1 {r h : ℕ} (hr : 40901 ≤ r) (hh : h ≤ 1) :
    2 ^ (175 + 6 * h) * r ^ 59 < 3 ^ (r / 50 + 1) :=
  lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (big_r50 hr)

/-- `⌊r/50⌋ + 1 < ⌊r/d⌋` for `0 < d < 16`, `r ≥ 40901`. -/
theorem N50_lt {r d : ℕ} (hr : 40901 ≤ r) (hd0 : 0 < d) (hd : d < 16) : r / 50 + 1 < r / d :=
  lt_of_lt_of_le (by omega : r / 50 + 1 < r / 15) (Nat.div_le_div_left (by omega) hd0)

/-! ### Start-free cycle forms -/

section Cycle
open CollatzProof

/-- **Start-free cycle form of T2b.** No positive `T`-cycle (`r ≥ 2` odd steps, period `L`)
has a valuation word which, read from ANY start `k`, has height `≤ h` about `chr r L` and is
piecewise Christoffel (arbitrary slopes) with cut set `P`, `|P| · ℓ < r`,
`ℓ ≥ N + 2g + 3`, `g + 1 ≤ N < r / gcd(L, r)`, `2^{175+6h} r^59 < 3^{g+1}`.
Scope: cycle level = Terras + max bound (see the module docstring); real cycles are not known to
have bounded height. -/
theorem cycle_chr_pieces_rot {m L r k h g N ℓ : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hup : ∀ j < r, psum (NormLebel.rot r k v) j ≤ j * L / r + h)
    (hdn : ∀ j < r, j * L / r ≤ psum (NormLebel.rot r k v) j + h)
    (P : Finset ℕ) (hP : ∀ e ∈ P, e < r) (hcount : P.card * ℓ < r)
    (hpw : ∀ x < r, (∀ j < r, arc r x ℓ j → j ∉ P) →
      ∃ s p c, 1 ≤ s ∧ ∀ k' < ℓ, NormLebel.rot r k v ((x + k') % r) = NormGoal.chr s p (c + k'))
    (hgN : g + 1 ≤ N) (hN : N < r / Nat.gcd L r) (hlen : N + 2 * g + 3 ≤ ℓ) (hℓ : ℓ ≤ r)
    (hbig : 2 ^ (175 + 6 * h) * r ^ 59 < 3 ^ (g + 1)) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨h1, h2, h3⟩ := NormPlateauLift.rot_facts (k := k) hr hv1 hL hq hdiv
  exact chr_pieces hq h1 h2 hup hdn P hP hcount hpw hgN hN hlen hℓ
    (gap_all59 (by omega) (by omega)) hbig h3

/-- **Explicit instance.** No nontrivial (`m ≠ 1`) positive `T`-cycle with `gcd(L, r) < 16`
has a valuation word (any start) of height `≤ 1` that is piecewise Christoffel with arbitrary
slopes and `|P| · (3⌊r/50⌋ + 4) < r` cuts (about `16` pieces). The point is the arbitrary slopes
and unbounded number of level changes, not the number `16`.
Scope: cycle level = Terras + max bound. -/
theorem cycle_chr_pieces_big {m L r k h : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hm : m ≠ 1)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hd : Nat.gcd L r < 16) (hh : h ≤ 1)
    (hup : ∀ j < r, psum (NormLebel.rot r k v) j ≤ j * L / r + h)
    (hdn : ∀ j < r, j * L / r ≤ psum (NormLebel.rot r k v) j + h)
    (P : Finset ℕ) (hP : ∀ e ∈ P, e < r) (hcount : P.card * (3 * (r / 50) + 4) < r)
    (hpw : ∀ x < r, (∀ j < r, arc r x (3 * (r / 50) + 4) j → j ∉ P) →
      ∃ s p c, 1 ≤ s ∧ ∀ k' < 3 * (r / 50) + 4,
        NormLebel.rot r k v ((x + k') % r) = NormGoal.chr s p (c + k')) : False := by
  obtain ⟨-, hr4⟩ := NormCycleAll.cycle_params (by omega) hv1 hL hodd hcyc hm
  exact cycle_chr_pieces_rot (g := r / 50) (N := r / 50 + 1) hr hv1 hL hodd hcyc hup hdn P hP
    hcount hpw le_rfl (N50_lt hr4 (Nat.gcd_pos_of_pos_right _ (by omega)) hd) (by omega)
    (by omega) (hbig50_of_le1 hr4 hh)

end Cycle

/-! ### Non-vacuity -/

set_option maxRecDepth 100000 in
/-- **Witness with nonzero deviation (fix F1).** For `r = 40903`, `A = 64830` (coprime),
`v = slide (chr r A) 1 20001` (one unit moved from position `1` to position `20001`), `h = 1`,
`g = 818`, `N = 819`, `ℓ = 2458`, the arc `[2, 2460)` and the piece `chr r A` read from `c = 2`:
every hypothesis of `chr_piece` holds, and the deviation `ε = -1` on that arc (shown at
`ρ = 2`). So `chr_piece` (hence `rep_factor_gap`) is non-vacuous at a word that is not
Christoffel. (The conclusion was already known from `NormShift` `no_cycle_slide_coprime`.) -/
theorem chr_piece_witness :
    eps 40903 64830 (NormGoal.slide (NormGoal.chr 40903 64830) 1 20001) 2 = -1 ∧
    ¬ (2 ^ 64830 - 3 ^ 40903) ∣ Bnum 40903 (NormGoal.slide (NormGoal.chr 40903 64830) 1 20001) := by
  have hq : 3 ^ 40903 + 1 < 2 ^ 64830 := by decide +kernel
  have hc : Nat.gcd 64830 40903 = 1 := by decide +kernel
  have h2 : 2 ≤ NormGoal.chr 40903 64830 1 := by unfold NormGoal.chr; norm_num
  obtain ⟨hv1, hA, hps⟩ := NormPlateau.slide_facts hq (by norm_num : 1 < 40903)
    (by norm_num : 20001 < 40903) (by norm_num) h2
  refine ⟨?_, ?_⟩
  · have := hps 2
    simp only [show (1 : ℕ) < 2 by norm_num, show ¬ (20001 : ℕ) < 2 by norm_num, ite_true,
      ite_false] at this
    unfold eps; omega
  refine chr_piece (h := 1) (g := 818) (N := 819) (ℓ := 2458) (x := 2) (s := 40903) (p := 64830)
    (c := 2) hq hv1 hA ?_ ?_ (by norm_num) (by norm_num) (by rw [hc]; norm_num) (by norm_num)
    (by norm_num) ?_ (gap_all59 (by norm_num) (by omega)) (by decide +kernel)
  · intro j _; have := hps j; split_ifs at this <;> omega
  · intro j _; have := hps j; split_ifs at this <;> omega
  · intro k hk
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold NormGoal.slide
    rw [if_neg (by omega), if_neg (by omega)]

end Collatz.NormFactor

#print axioms Collatz.NormFactor.rep_factor
#print axioms Collatz.NormFactor.rep_factor_gap
#print axioms Collatz.NormFactor.chr_rep
#print axioms Collatz.NormFactor.chr_piece
#print axioms Collatz.NormFactor.chr_pieces
#print axioms Collatz.NormFactor.big_r50
#print axioms Collatz.NormFactor.cycle_chr_pieces_rot
#print axioms Collatz.NormFactor.cycle_chr_pieces_big
#print axioms Collatz.NormFactor.chr_piece_witness
