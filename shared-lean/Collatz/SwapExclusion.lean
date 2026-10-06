import Collatz.SwapCore
import CycleLenPoly59
import Farey25

/-!
# SwapExclusion: no two cycle points with parity words one local move apart

Let `x, y > 0` be `T`-periodic with a common period `L` (not necessarily minimal; `x = y`
rotations and points of different cycles are both covered). Write `w = pw_L x`, `w' = pw_L y`.

* `no_single_swap` (T2a): `w = P·10·S`, `w' = P·01·S` ⇒ `x, y ≤ 2`. Elementary:
  `D ∣ ρ(w') - ρ(w) = 2^p 3^s`, `gcd(D,6) = 1`, so `D = 1`, `(L,k) = (2,1)`.
  **Formalization of a likely-known Knight-type mechanism; not claimed new.**
* `no_double_swap`, `no_same_swap`, `no_slide_false`, `no_slide_true` (T2b): opposite /
  same-direction double swap, slide of a 0 across `r ≥ 1` ones, slide of a 1 across `r ≥ 1`
  zeros ⇒ `x, y ≤ 2`. Proof: `D` divides the binomial `3^u ∓ 2^V` of `SwapCore`, the partner
  congruence gives `D ∣ 2^{L-V} ∓ 3^{k-u}`, so `D^2 ≤ 4·3^L` (`partner_bound_*`); with
  `gap_all59` this gives `4^L ≤ 2^346 L^116 3^L`, false for `L ≥ 18445` (`growth_116`), while
  a non-trivial `x` has `L ≥ 18445` (`T_period_ge`: `C`-length `≤ 2L` plus
  `cycleLengthAtLeast_36890`). **Plausibly new, thin, unconfirmed.**

Helper `exists_iterate_C_le_two_mul`: `j` Terras steps are `i` Collatz steps with `j ≤ i ≤ 2j`
(used instead of the exact `C^[L+k] = T^[L]` of the plan; it suffices).

Draft: `Scratch/SwapExclusionDev.lean`.
-/

namespace Collatz
open CollatzProof

/-- Every `j` Terras steps are between `j` and `2j` Collatz steps. -/
theorem exists_iterate_C_le_two_mul (j x : ℕ) : ∃ i, j ≤ i ∧ i ≤ 2 * j ∧ C^[i] x = T^[j] x := by
  induction j generalizing x with
  | zero => exact ⟨0, le_rfl, le_rfl, rfl⟩
  | succ j ih =>
    obtain ⟨i', h1, h2, hi'⟩ := ih (T x)
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · refine ⟨i' + 1, by omega, by omega, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hi', T_eq_C_of_even h]
    · refine ⟨i' + 2, by omega, by omega, ?_⟩
      rw [show i' + 2 = i' + 1 + 1 from rfl, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        ← T_eq_C_C_of_odd (by omega), hi']

/-- A positive non-trivial `T`-periodic point with period `L` forces `L ≥ 18445`
(from `cycleLengthAtLeast_36890` and `C`-length `≤ 2L`). -/
theorem T_period_ge {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (h : T^[L] x = x) (hx2 : 2 < x) :
    18445 ≤ L := by
  obtain ⟨i, h1, h2, hi⟩ := exists_iterate_C_le_two_mul L x
  rw [h] at hi
  have h4 : x ≠ 4 := by
    rintro rfl; exact not_T_cycle_four hL h
  have := cycleLengthAtLeast_36890 x i hx (by omega) hi (by omega) (by omega) h4
  omega

set_option exponentiation.threshold 1000 in
/-- Growth: `2^346 · L^116 · 3^L < 4^L` for `L ≥ 18445`. -/
theorem growth_116 {L : ℕ} (hL : 18445 ≤ L) : 2^346 * L^116 * 3^L < 4^L := by
  induction L, hL using Nat.le_induction with
  | base =>
    set_option exponentiation.threshold 40000 in norm_num
  | succ L hL ih =>
    have h1 : (L+1)*500 ≤ 501*L := by omega
    have h2 : ((L+1)*500)^116 ≤ (501*L)^116 := Nat.pow_le_pow_left h1 116
    have h3 : 3 * 501^116 ≤ 4 * 500^116 := by norm_num
    have h4 : 3 * (L+1)^116 ≤ 4 * L^116 := by
      rw [mul_pow, mul_pow] at h2
      have hp : 0 < 500^116 := by positivity
      have : 3 * (L+1)^116 * 500^116 ≤ 4 * L^116 * 500^116 := by
        calc 3 * (L+1)^116 * 500^116 = 3 * ((L+1)^116 * 500^116) := by ring
          _ ≤ 3 * (501^116 * L^116) := Nat.mul_le_mul_left _ h2
          _ = (3 * 501^116) * L^116 := by ring
          _ ≤ (4 * 500^116) * L^116 := Nat.mul_le_mul_right _ h3
          _ = 4 * L^116 * 500^116 := by ring
      exact Nat.le_of_mul_le_mul_right this hp
    calc 2^346 * (L+1)^116 * 3^(L+1) = 2^346 * (3 * (L+1)^116) * 3^L := by ring
      _ ≤ 2^346 * (4 * L^116) * 3^L := by gcongr
      _ = 4 * (2^346 * L^116 * 3^L) := by ring
      _ < 4 * 4^L := by omega
      _ = 4^(L+1) := by ring

set_option exponentiation.threshold 1000 in
/-- **Core.** A positive `T`-periodic point `x` (period `L`, `k ≥ 1` odd steps) with
`(2^L - 3^k)^2 ≤ 4·3^L` is `≤ 2`. -/
theorem le_two_of_D_sq_le {x L : ℕ} (hx : 0 < x) (h : T^[L] x = x) (hk : 0 < oddSteps L x)
    (hD : ((2:ℤ)^L - 3^(oddSteps L x))^2 ≤ 4 * 3^L) : x ≤ 2 := by
  by_contra hx2
  simp only [not_le] at hx2
  set k := oddSteps L x with hkdef
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp [hkdef, oddSteps] at hk
    · exact h0
  have h3 : 3^k < 2^L := three_pow_lt_two_pow_of_cycle hx hL h
  have hkL : k < L := by
    by_contra hc
    have h1 : 3^L ≤ 3^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2^L ≤ 3^L := Nat.pow_le_pow_left (by norm_num) L
    omega
  have hL0 := T_period_ge hx hL h hx2
  have hgap := gap_all59 hk h3
  have hDn : (2^L - 3^k)^2 ≤ 4 * 3^L := by
    have : (((2^L - 3^k : ℕ) : ℤ))^2 ≤ ((4 * 3^L : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h3.le]; exact hD
    exact_mod_cast this
  have hsq : (2^L)^2 ≤ (2^172 * k^58 * (2^L - 3^k))^2 := Nat.pow_le_pow_left hgap 2
  have hk116 : k^116 ≤ L^116 := Nat.pow_le_pow_left hkL.le 116
  have e4 : (4:ℕ)^L = (2^L)^2 := by rw [← pow_mul, show (4:ℕ) = 2^2 by rfl, ← pow_mul, mul_comm]
  have hg := growth_116 hL0
  have : (4:ℕ)^L ≤ 2^346 * L^116 * 3^L := by
    calc (4:ℕ)^L = (2^L)^2 := e4
      _ ≤ (2^172 * k^58 * (2^L - 3^k))^2 := hsq
      _ = 2^344 * k^116 * (2^L - 3^k)^2 := by ring
      _ ≤ 2^344 * k^116 * (4 * 3^L) := by gcongr
      _ = 2^346 * k^116 * 3^L := by ring
      _ ≤ 2^346 * L^116 * 3^L := by gcongr
  omega

/-- `3^a - 2^b ≠ 0` in ℤ for `b ≥ 1` (parity). -/
theorem three_pow_sub_two_pow_ne {a b : ℕ} (hb : 0 < b) : (3:ℤ)^a - 2^b ≠ 0 := by
  intro h
  have h1 : ((3^a : ℕ) : ℤ) = ((2^b : ℕ) : ℤ) := by push_cast; linarith
  have h2 : 3^a = 2^b := by exact_mod_cast h1
  have h3 : 3^a % 2 = 1 := by rw [Nat.pow_mod]; simp
  have h4 : 2^b % 2 = 0 := by
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [pow_succ]; simp
  omega

/-- `2^b - 3^a ≠ 0` in ℤ for `b ≥ 1`. -/
theorem two_pow_sub_three_pow_ne {a b : ℕ} (hb : 0 < b) : (2:ℤ)^b - 3^a ≠ 0 := by
  intro h; exact three_pow_sub_two_pow_ne (a := a) hb (by linarith)

/-- Two points of `T`-cycles with common period `L` and equal odd-step count `k`:
`D = 2^L - 3^k` divides `ρ(pw_L y) - ρ(pw_L x)`. -/
theorem D_dvd_rhoW_sub {x y L : ℕ} (hxL : T^[L] x = x) (hyL : T^[L] y = y)
    (h3 : 3^(oddSteps L x) < 2^L) (hc : oddSteps L y = oddSteps L x) :
    ((2:ℤ)^L - 3^(oddSteps L x)) ∣ (rhoW (parityWord L y) : ℤ) - rhoW (parityWord L x) := by
  have ex := cycle_eq_word hxL
  have ey := cycle_eq_word hyL
  rw [hc] at ey
  have cx : (((2^L - 3^(oddSteps L x)) * x : ℕ) : ℤ) = (rhoW (parityWord L x) : ℤ) := by
    rw [ex]
  have cy : (((2^L - 3^(oddSteps L x)) * y : ℕ) : ℤ) = (rhoW (parityWord L y) : ℤ) := by
    rw [ey]
  push_cast [Nat.cast_sub h3.le] at cx cy
  exact ⟨(y:ℤ) - x, by rw [← cx, ← cy]; ring⟩

/-- Finishing step shared by all moves. -/
theorem pair_le_two {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hxL : T^[L] x = x)
    (hyL : T^[L] y = y) (hc : oddSteps L y = oddSteps L x) (hk : 0 < oddSteps L x)
    (hD : ((2:ℤ)^L - 3^(oddSteps L x))^2 ≤ 4 * 3^L) : x ≤ 2 ∧ y ≤ 2 :=
  ⟨le_two_of_D_sq_le hx hxL hk hD, le_two_of_D_sq_le hy hyL (hc ▸ hk) (hc ▸ hD)⟩

/-- **T2a: single adjacent swap** (formalization of a likely-known Knight-type mechanism).
If `x, y > 0` have common `T`-period `L` and their length-`L` parity words are
`P·10·S` and `P·01·S`, then `x, y ≤ 2`. Elementary: `D ∣ 2^p 3^s` forces `D = 1`,
so `(L,k) = (2,1)`. -/
theorem no_single_swap {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hxL : T^[L] x = x)
    (hyL : T^[L] y = y) (P S : List Bool)
    (hw : parityWord L x = P ++ [true, false] ++ S)
    (hw' : parityWord L y = P ++ [false, true] ++ S) : x ≤ 2 ∧ y ≤ 2 := by
  have hlen := length_parityWord L x
  have hcx := count_parityWord L x
  have hcy := count_parityWord L y
  rw [hw] at hlen hcx; rw [hw'] at hcy
  simp [List.count_append] at hlen hcx hcy
  have hc : oddSteps L y = oddSteps L x := by omega
  have hk : 0 < oddSteps L x := by omega
  have hL : 0 < L := by omega
  have h3 := three_pow_lt_two_pow_of_cycle hx hL hxL
  have hd := D_dvd_rhoW_sub hxL hyL h3 hc
  rw [hw, hw', swap_one, ← mul_one ((2:ℤ)^P.length * 3^S.count true)] at hd
  have hd1 := D_dvd_of_dvd_unit_mul hk hL hd
  have hDpos : (0:ℤ) < 2^L - 3^(oddSteps L x) := by
    have : ((3^(oddSteps L x) : ℕ) : ℤ) < ((2^L : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at this; linarith
  have hD1 : (2:ℤ)^L - 3^(oddSteps L x) = 1 := Int.eq_one_of_dvd_one hDpos.le hd1
  have hN : 2^L = 3^(oddSteps L x) + 1 := by
    have : ((2^L : ℕ) : ℤ) = ((3^(oddSteps L x) + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨hL2, hk1⟩ := pow2_eq_pow3_add_one hN hk
  have ux := cycle_point_upper hxL
  have uy := cycle_point_upper hyL
  rw [hc] at uy
  rw [hk1, hL2] at ux uy
  norm_num at ux uy
  omega

/-- **T2b (i): opposite double swap** (plausibly new, unconfirmed). If `x, y > 0` have common
`T`-period `L` and parity words `P·10·M·01·S` and `P·01·M·10·S`, then `x, y ≤ 2`. -/
theorem no_double_swap {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hxL : T^[L] x = x)
    (hyL : T^[L] y = y) (P M S : List Bool)
    (hw : parityWord L x = P ++ [true, false] ++ M ++ [false, true] ++ S)
    (hw' : parityWord L y = P ++ [false, true] ++ M ++ [true, false] ++ S) :
    x ≤ 2 ∧ y ≤ 2 := by
  have hlen := length_parityWord L x
  have hcx := count_parityWord L x
  have hcy := count_parityWord L y
  rw [hw] at hlen hcx; rw [hw'] at hcy
  simp [List.count_append] at hlen hcx hcy
  have hP := List.count_le_length (a := true) (l := P)
  have hM := List.count_le_length (a := true) (l := M)
  have hS := List.count_le_length (a := true) (l := S)
  have hc : oddSteps L y = oddSteps L x := by omega
  have hk : 0 < oddSteps L x := by omega
  have hL : 0 < L := by omega
  have h3 := three_pow_lt_two_pow_of_cycle hx hL hxL
  have hd := D_dvd_rhoW_sub hxL hyL h3 hc
  rw [hw, hw', swap_opp] at hd
  have hd1 := D_dvd_of_dvd_unit_mul hk hL hd
  refine pair_le_two hx hy hxL hyL hc hk ?_
  exact partner_bound_minus h3 (by omega) (by omega) (by omega) (by omega)
    (three_pow_sub_two_pow_ne (by omega)) (two_pow_sub_three_pow_ne (by omega)) hd1

/-- **T2b (ii): same-direction double swap** (plausibly new, unconfirmed). Parity words
`P·10·M·10·S` and `P·01·M·01·S` ⇒ `x, y ≤ 2`. (The trivial cycle, `1010`/`0101`, shows that
the non-trivial-cycle length input is needed here: `7 ∣ 3 + 4`.) -/
theorem no_same_swap {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hxL : T^[L] x = x)
    (hyL : T^[L] y = y) (P M S : List Bool)
    (hw : parityWord L x = P ++ [true, false] ++ M ++ [true, false] ++ S)
    (hw' : parityWord L y = P ++ [false, true] ++ M ++ [false, true] ++ S) :
    x ≤ 2 ∧ y ≤ 2 := by
  have hlen := length_parityWord L x
  have hcx := count_parityWord L x
  have hcy := count_parityWord L y
  rw [hw] at hlen hcx; rw [hw'] at hcy
  simp [List.count_append] at hlen hcx hcy
  have hP := List.count_le_length (a := true) (l := P)
  have hM := List.count_le_length (a := true) (l := M)
  have hS := List.count_le_length (a := true) (l := S)
  have hc : oddSteps L y = oddSteps L x := by omega
  have hk : 0 < oddSteps L x := by omega
  have hL : 0 < L := by omega
  have h3 := three_pow_lt_two_pow_of_cycle hx hL hxL
  have hd := D_dvd_rhoW_sub hxL hyL h3 hc
  rw [hw, hw', swap_same] at hd
  have hd1 := D_dvd_of_dvd_unit_mul hk hL hd
  refine pair_le_two hx hy hxL hyL hc hk ?_
  exact partner_bound_plus h3 (by omega) (by omega) (by omega) (by omega) hd1

/-- **T2b (iii): slide of a 0 across `r ≥ 1` ones** (plausibly new for `r ≥ 2`; `r = 1` is the
single swap). Parity words `P·1^r·0·S` and `P·0·1^r·S` ⇒ `x, y ≤ 2`. -/
theorem no_slide_false {x y L r : ℕ} (hx : 0 < x) (hy : 0 < y) (hxL : T^[L] x = x)
    (hyL : T^[L] y = y) (hr : 0 < r) (P S : List Bool)
    (hw : parityWord L x = P ++ List.replicate r true ++ [false] ++ S)
    (hw' : parityWord L y = P ++ [false] ++ List.replicate r true ++ S) :
    x ≤ 2 ∧ y ≤ 2 := by
  have hlen := length_parityWord L x
  have hcx := count_parityWord L x
  have hcy := count_parityWord L y
  rw [hw] at hlen hcx; rw [hw'] at hcy
  simp [List.count_append] at hlen hcx hcy
  have hP := List.count_le_length (a := true) (l := P)
  have hS := List.count_le_length (a := true) (l := S)
  have hc : oddSteps L y = oddSteps L x := by omega
  have hk : 0 < oddSteps L x := by omega
  have hL : 0 < L := by omega
  have h3 := three_pow_lt_two_pow_of_cycle hx hL hxL
  have hd := D_dvd_rhoW_sub hxL hyL h3 hc
  rw [hw, hw', slide_false] at hd
  have hd1 := D_dvd_of_dvd_unit_mul hk hL hd
  refine pair_le_two hx hy hxL hyL hc hk ?_
  exact partner_bound_minus h3 le_rfl (by omega) (by omega) (by omega)
    (three_pow_sub_two_pow_ne hr) (two_pow_sub_three_pow_ne (by omega)) hd1

/-- **T2b (iv): slide of a 1 across `r ≥ 1` zeros** (plausibly new for `r ≥ 2`). Parity words
`P·0^r·1·S` and `P·1·0^r·S` ⇒ `x, y ≤ 2`. -/
theorem no_slide_true {x y L r : ℕ} (hx : 0 < x) (hy : 0 < y) (hxL : T^[L] x = x)
    (hyL : T^[L] y = y) (hr : 0 < r) (P S : List Bool)
    (hw : parityWord L x = P ++ List.replicate r false ++ [true] ++ S)
    (hw' : parityWord L y = P ++ [true] ++ List.replicate r false ++ S) :
    x ≤ 2 ∧ y ≤ 2 := by
  have hlen := length_parityWord L x
  have hcx := count_parityWord L x
  have hcy := count_parityWord L y
  rw [hw] at hlen hcx; rw [hw'] at hcy
  simp [List.count_append, List.count_replicate] at hlen hcx hcy
  have hP := List.count_le_length (a := true) (l := P)
  have hS := List.count_le_length (a := true) (l := S)
  have hc : oddSteps L y = oddSteps L x := by omega
  have hk : 0 < oddSteps L x := by omega
  have hL : 0 < L := by omega
  have h3 := three_pow_lt_two_pow_of_cycle hx hL hxL
  have hd := D_dvd_rhoW_sub hxL hyL h3 hc
  rw [hw, hw'] at hd
  have hd' := dvd_neg.mpr hd
  rw [neg_sub, slide_true] at hd'
  have hd1 := D_dvd_of_dvd_unit_mul hk hL hd'
  have hd2 : ((2:ℤ)^L - 3^(oddSteps L x)) ∣ (3:ℤ)^0 - 2^r := by
    have := dvd_neg.mpr hd1
    simpa using this
  refine pair_le_two hx hy hxL hyL hc hk ?_
  exact partner_bound_minus h3 (Nat.zero_le _) (by omega) (Nat.zero_le _) (by omega)
    (three_pow_sub_two_pow_ne hr) (two_pow_sub_three_pow_ne (by omega)) hd2

/-- Sanity: the trivial cycle `1 → 2 → 1` read with period 4 has parity words `1010`, `0101`
(a same-direction double swap); the conclusion `x, y ≤ 2` holds. -/
example : (1:ℕ) ≤ 2 ∧ (2:ℕ) ≤ 2 :=
  no_same_swap (x := 1) (y := 2) (L := 4) (by norm_num) (by norm_num) (by decide) (by decide)
    [] [] [] (by decide) (by decide)

end Collatz

#print axioms Collatz.exists_iterate_C_le_two_mul
#print axioms Collatz.T_period_ge
#print axioms Collatz.growth_116
#print axioms Collatz.le_two_of_D_sq_le
#print axioms Collatz.D_dvd_rhoW_sub
#print axioms Collatz.no_single_swap
#print axioms Collatz.no_double_swap
#print axioms Collatz.no_same_swap
#print axioms Collatz.no_slide_false
#print axioms Collatz.no_slide_true
