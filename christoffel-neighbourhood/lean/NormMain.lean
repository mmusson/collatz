import NormReduce
import NormDet
import NormFinite
import CollatzSearch.FareyStretch
import CollatzSearch.SwapExclusion

/-!
# proof of the MAIN GOAL `no_cycle_one_move_christoffel`

For coprime `r ≥ 2` and `A` with `3^r + 1 < 2^A`, no word one cyclic adjacent swap or one
slide away from the lower Christoffel word `chr r A` satisfies `(2^A - 3^r) ∣ B`.

Route (elementary norm argument, no resultants or Mahler measure):
1. `NormReduce.reduce`: `q ∣ B(v)` forces `g^(p+1) - g^p + 1 = 0` or `g^e - g + 1 = 0` at the
   unique `g ∈ ZMod q` with `g^r = 2`, `g^A = 3`; for `A < 2r` the exponents are `≤ A - r`.
2. `NormDet.le_typeI/II`: the companion matrix `Sh(a) - Sh(b) + 1` has odd determinant
   divisible by `q`, and `det^2 r^r ≤ ‖·‖_F^{2r}`, so `q^2 r^r ≤ (3r + 3a + 3b)^r`.
3. Case `2^A > 2·3^r`: `q > 3^r` beats the bound `(9r)^r`; the two edge exponents
   (`p = r-1`, `e = r`) give `q ∣ 2^(A+1-r) - 1` resp. `q ∣ 3^r - 2`, both too small.
   Case `2^A ≤ 2·3^r` (`A < 2r`): `r < 150` by the kernel table `NormFinite.finite_check`;
   `150 ≤ r < 225644606` by `gapBelow_225644606` (`2^A ≤ 2^30 q`); larger `r` by `gap_all59`
   (`2^A ≤ 2^172 r^58 q`) and `growth_116`.

This is a statement about cycle WORDS (the divisibility `q ∣ B` that every positive cycle with
that word would satisfy). It is NOT `no_nontrivial_cycles` and not a milestone.
-/

namespace CollatzSearch.NormMain
open CollatzSearch.NormGoal CollatzSearch.NormReduce CollatzSearch.NormDet

theorem ratio_small {r : ℕ} (hr : 150 ≤ r) : (2 ^ 30) ^ 2 * 6600 ^ r < 9000 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r _ ih =>
    rw [pow_succ, pow_succ]
    calc (2 ^ 30) ^ 2 * (6600 ^ r * 6600) = ((2 ^ 30) ^ 2 * 6600 ^ r) * 6600 := by ring
      _ < 9000 ^ r * 6600 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ 9000 ^ r * 9000 := Nat.mul_le_mul_left _ (by norm_num)

theorem ratio_big {r : ℕ} (hr : 18445 ≤ r) : (2 ^ 172 * r ^ 58) ^ 2 * 6600 ^ r < 9000 ^ r := by
  have g := growth_116 hr
  have h1 : 2 ^ 346 * r ^ 116 * 3 ^ r * 6600 ^ r < 4 ^ r * 6600 ^ r :=
    Nat.mul_lt_mul_of_pos_right g (by positivity)
  have h2 : 4 ^ r * 6600 ^ r ≤ 9000 ^ r * 3 ^ r := by
    rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) r
  have h3 : (2 ^ 172 * r ^ 58) ^ 2 * 6600 ^ r * 3 ^ r ≤ 2 ^ 346 * r ^ 116 * 3 ^ r * 6600 ^ r := by
    have : (2 ^ 172 * r ^ 58) ^ 2 = 2 ^ 344 * r ^ 116 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [this]
    have h346 : (2:ℕ) ^ 346 = 2 ^ 344 * 4 := by rw [show 346 = 344 + 2 from rfl, pow_add]; norm_num
    have : 2 ^ 344 * r ^ 116 * 6600 ^ r * 3 ^ r * 4 = 2 ^ 346 * r ^ 116 * 3 ^ r * 6600 ^ r := by
      rw [h346]; ring
    omega
  exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h3 (lt_of_lt_of_le h1 h2))

theorem two_mul_three_pow_lt {r : ℕ} (hr : 3 ≤ r) : 2 * 3 ^ r < 4 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r _ ih => rw [pow_succ, pow_succ]; omega

/-- The analytic contradiction for `r ≥ 100` from a gap `2^A ≤ K q`. -/
theorem big_contra {r A q K F : ℕ} (hr : 100 ≤ r) (h3 : 3 ^ r < 2 ^ A) (hA2 : 2 ^ A ≤ 2 * 3 ^ r)
    (hgap : 2 ^ A ≤ K * q) (hF : q ^ 2 * r ^ r ≤ F ^ r) (hFle : F + 3 * r ≤ 6 * A + 3)
    (hK : K ^ 2 * 6600 ^ r < 9000 ^ r) : False := by
  have hA1 : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; simp at h3
    · exact h
  have hA1000 : 1000 * (A - 1) < 1585 * r := by
    have e1 : 2 ^ (A - 1) ≤ 3 ^ r := by
      have : 2 ^ A = 2 * 2 ^ (A - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    have e2 : 2 ^ (1000 * (A - 1)) < 2 ^ (1585 * r) := by
      calc 2 ^ (1000 * (A - 1)) = (2 ^ (A - 1)) ^ 1000 := by rw [← pow_mul, mul_comm]
        _ ≤ (3 ^ r) ^ 1000 := Nat.pow_le_pow_left e1 _
        _ = (3 ^ 1000) ^ r := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ < (2 ^ 1585) ^ r := Nat.pow_lt_pow_left
            (by set_option exponentiation.threshold 2000 in norm_num) (by omega)
        _ = 2 ^ (1585 * r) := by rw [← pow_mul, mul_comm]
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp e2
  have hF2 : 1000 * F ≤ 6600 * r := by omega
  have e1 : (3 ^ r) ^ 2 < (2 ^ A) ^ 2 := Nat.pow_lt_pow_left h3 two_ne_zero
  have e2 : (2 ^ A) ^ 2 ≤ K ^ 2 * q ^ 2 := by rw [← mul_pow]; exact Nat.pow_le_pow_left hgap 2
  have hrr : 0 < r ^ r := by positivity
  have h1000 : 0 < 1000 ^ r := by positivity
  have c1 : 9000 ^ r * r ^ r < K ^ 2 * 6600 ^ r * r ^ r := by
    have h9 : (3 ^ r) ^ 2 * 1000 ^ r = 9000 ^ r := by
      rw [← pow_mul, mul_comm r 2, pow_mul, ← mul_pow]; norm_num
    calc 9000 ^ r * r ^ r = (3 ^ r) ^ 2 * 1000 ^ r * r ^ r := by rw [h9]
      _ < (2 ^ A) ^ 2 * 1000 ^ r * r ^ r :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right e1 h1000) hrr
      _ ≤ K ^ 2 * q ^ 2 * 1000 ^ r * r ^ r :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ e2)
      _ = K ^ 2 * 1000 ^ r * (q ^ 2 * r ^ r) := by ring
      _ ≤ K ^ 2 * 1000 ^ r * F ^ r := Nat.mul_le_mul_left _ hF
      _ = K ^ 2 * (1000 * F) ^ r := by rw [mul_pow]; ring
      _ ≤ K ^ 2 * (6600 * r) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hF2 r)
      _ = K ^ 2 * 6600 ^ r * r ^ r := by rw [mul_pow]; ring
  have c2 := Nat.lt_of_mul_lt_mul_right c1
  omega

/-- **MAIN GOAL.** For coprime `r ≥ 2` and `A` with `3^r + 1 < 2^A`, no word `v`
one cyclic adjacent swap or one slide away from the lower Christoffel word `chr r A` satisfies
`(2^A - 3^r) ∣ B(v)`. Same statement as `NormGoal.no_cycle_one_move_christoffel`. -/
theorem main (r A : ℕ) (hr : 2 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (v : ℕ → ℕ) (hv : OneMove r (chr r A) v) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  obtain ⟨g, h2, h3⟩ := exists_g (by omega) hcop hq
  have hred := reduce hr hcop hq h2 h3 hv hdiv
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  have h32 := three_r_le_two_A hq
  have hAr := r_lt_A hq
  by_cases hbig : 2 * 3 ^ r < 2 ^ A
  · -- case (i): q > 3^r
    have hq3 : 3 ^ r < 2 ^ A - 3 ^ r := by omega
    have hsq : (3 ^ r) ^ 2 < (2 ^ A - 3 ^ r) ^ 2 := Nat.pow_lt_pow_left hq3 two_ne_zero
    have kill : ∀ F, F < 9 * r → (2 ^ A - 3 ^ r) ^ 2 * r ^ r ≤ F ^ r → False := by
      intro F hF hle
      have k1 : F ^ r < (9 * r) ^ r := Nat.pow_lt_pow_left hF (by omega)
      have k2 : (9 * r) ^ r = (3 ^ r) ^ 2 * r ^ r := by
        rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul]; norm_num
      have k3 : (3 ^ r) ^ 2 * r ^ r < (2 ^ A - 3 ^ r) ^ 2 * r ^ r :=
        Nat.mul_lt_mul_of_pos_right hsq (by positivity)
      omega
    rcases hred with ⟨p, hp1, hpr, -, hp⟩ | ⟨e, he2, her, -, he⟩
    · by_cases hpr' : p + 1 < r
      · have := le_typeI hq1 hp1 hpr' g h2 hp
        exact kill (3 * r + 6 * p + 3) (by omega) (by exact_mod_cast this)
      · -- p = r - 1: forces `q ∣ 2^(A+1-r) - 1`
        have hpe : p + 1 = r := by omega
        rw [hpe, h2] at hp
        have hg3 : g ^ p = 3 := by linear_combination -hp
        have hgr : g ^ (p + 1) = g ^ r := by congr 1
        have hg32 : 3 * g = 2 := by rw [← hg3, ← pow_succ, hgr, h2]
        have h4 : (3 : ZMod (2 ^ A - 3 ^ r)) ^ r * 2 = 2 ^ r := by
          calc (3 : ZMod (2 ^ A - 3 ^ r)) ^ r * 2 = 3 ^ r * g ^ r := by rw [h2]
            _ = (3 * g) ^ r := (mul_pow _ _ _).symm
            _ = 2 ^ r := by rw [hg32]
        rw [← two_pow_eq hq] at h4
        have h' : (2 : ZMod (2 ^ A - 3 ^ r)) ^ r * 2 ^ (A + 1 - r) = 2 ^ r * 1 := by
          rw [← pow_add, show r + (A + 1 - r) = A + 1 by omega, pow_succ, h4, mul_one]
        have h1 := ((isUnit_two hq).pow r).mul_left_cancel h'
        have hle1 : 1 ≤ 2 ^ (A + 1 - r) := Nat.one_le_two_pow
        have hdvd : (2 ^ A - 3 ^ r) ∣ 2 ^ (A + 1 - r) - 1 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hle1]
          push_cast; rw [h1]; ring
        have h22 : 2 ≤ 2 ^ (A + 1 - r) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (A + 1 - r) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle := Nat.le_of_dvd (by omega) hdvd
        have h5 : 2 ^ (A + 1 - r) ≤ 2 ^ (A - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h6 : 2 ^ A = 2 * 2 ^ (A - 1) := by rw [← pow_succ']; congr 1; omega
        omega
    · by_cases her' : e < r
      · have := le_typeII hq1 he2 her' g h2 he
        exact kill (3 * r + 3 * e + 3) (by omega) (by exact_mod_cast this)
      · -- e = r: forces `q ∣ 3^r - 2`
        have hee : e = r := by omega
        subst hee
        rw [h2] at he
        have hg : g = 3 := by linear_combination -he
        rw [hg] at h2
        have h9 : 9 ≤ 3 ^ e := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he2
        have hdvd : (2 ^ A - 3 ^ e) ∣ 3 ^ e - 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega)]
          push_cast; rw [h2]; ring
        have hle := Nat.le_of_dvd (by omega) hdvd
        omega
  · -- case (ii): 2^A ≤ 2·3^r, so A = A₀ < 2r
    rw [not_lt] at hbig
    have hr3 : 3 ≤ r := by
      by_contra hr2
      have hr2' : r = 2 := by omega
      subst hr2'
      have hA5 : A < 5 := by
        by_contra h5
        have : 2 ^ 5 ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hbig this; omega
      have hA4 : 3 < A := by
        by_contra h4
        have : 2 ^ A ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hq this; omega
      have : A = 4 := by omega
      subst this
      norm_num at hcop
    have hA2r : A < 2 * r := by
      have : 2 ^ A < 2 ^ (2 * r) := by
        rw [pow_mul]; norm_num; exact lt_of_le_of_lt hbig (two_mul_three_pow_lt hr3)
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    by_cases hsmall : r < 150
    · have hfin := NormFinite.finite_check hr3 hsmall hq hbig hcop h2 h3
      rcases hred with ⟨p, hp1, _, hpA, hp⟩ | ⟨e, he2, _, heA, he⟩
      · exact hfin.1 p hp1 (by have := hpA hA2r; omega) hp
      · exact hfin.2 e he2 (by have := heA hA2r; omega) he
    · have hF : ∃ F, F + 3 * r ≤ 6 * A + 3 ∧ (2 ^ A - 3 ^ r) ^ 2 * r ^ r ≤ F ^ r := by
        rcases hred with ⟨p, hp1, _, hpA, hp⟩ | ⟨e, he2, _, heA, he⟩
        · have hpA' := hpA hA2r
          have := le_typeI hq1 hp1 (by omega) g h2 hp
          exact ⟨3 * r + 6 * p + 3, by omega, by exact_mod_cast this⟩
        · have heA' := heA hA2r
          have := le_typeII hq1 he2 (by omega) g h2 he
          exact ⟨3 * r + 3 * e + 3, by omega, by exact_mod_cast this⟩
      obtain ⟨F, hFle, hFr⟩ := hF
      have h3A : 3 ^ r < 2 ^ A := by omega
      by_cases hmid : r < 225644606
      · have hgap := gapBelow_225644606 r A (by omega) hmid h3A
        exact big_contra (by omega) h3A hbig hgap hFr hFle (ratio_small (by omega))
      · have hgap := gap_all59 (k := r) (L := A) (by omega) h3A
        exact big_contra (by omega) h3A hbig hgap hFr hFle (ratio_big (by omega))

/-- The main goal, in the exact form of `NormGoal.no_cycle_one_move_christoffel`. -/
theorem no_cycle_one_move_christoffel (r A : ℕ) (hr : 2 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (v : ℕ → ℕ) (hv : OneMove r (chr r A) v) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v :=
  main r A hr hcop hq v hv

/-- Sanity check: the statement is literally the `NormGoal` statement. -/
example : type_of% @no_cycle_one_move_christoffel =
    type_of% @CollatzSearch.NormGoal.no_cycle_one_move_christoffel := rfl

end CollatzSearch.NormMain

#print axioms CollatzSearch.NormMain.main
#print axioms CollatzSearch.NormMain.no_cycle_one_move_christoffel

