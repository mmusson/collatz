import NormTwo

/-!
# the large-r size contradiction (threshold 224/25 = 8.96)

`NormTwo.size_contra` turns a Parseval/Hadamard bound `q^2 ≤ Q^r` (`q = 2^A - 3^r`) into a
contradiction when `Q ≤ 219/25 = 8.76`, for every `r ≥ 2325`. At the cycle level we always have
`r ≥ 40901` (`NormCycleAll.cycle_params`), and then the same argument works up to
`Q ≤ 224/25 = 8.96`:

* `B1`: `4·224^r < 225^r` (`r ≥ 320`);
* `B2`: `2^60·224^r < 225^r` (`r ≥ 9600`), by chunking `2·224^160 < 225^160` (no huge literal);
* `B3`: `2^344·r^116·224^r < 225^r` (`r ≥ 2621440`), base via the chunk lemma at
  `2621440 = 160·2^14`, step as in `NormTwo.G2`;
* `size_contra_big`: the size contradiction with threshold `224/25` (Farey gaps
  `gapBelow_225644606` for `r < 225644606`, `gap_all59` above);
* `t_le_big`: `θ^2 ≤ 1 + 3/40901`.

This is routine infrastructure (an effective irrationality measure of `log 3/log 2` combined
with a size comparison).
-/

namespace Collatz.NormBig
open Collatz.NormTwo

set_option exponentiation.threshold 400 in
/-- B1: `4·224^r < 225^r` for `r ≥ 320`. -/
theorem B1 {r : ℕ} (hr : 320 ≤ r) : 4 * 224 ^ r < 225 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r _ ih => rw [pow_succ, pow_succ]; omega

set_option exponentiation.threshold 200 in
theorem B2a : 2 * 224 ^ 160 < 225 ^ 160 := by norm_num

theorem chunk_pow {a b : ℕ} (h : 2 * a < b) {n : ℕ} (hn : 1 ≤ n) : 2 ^ n * a ^ n < b ^ n := by
  rw [← mul_pow]
  exact Nat.pow_lt_pow_left h (by omega)

/-- B2b: `2^n·224^{160n} < 225^{160n}` for `n ≥ 1` (chunking, no big literal). -/
theorem B2b {n : ℕ} (hn : 1 ≤ n) : 2 ^ n * 224 ^ (160 * n) < 225 ^ (160 * n) := by
  rw [pow_mul, pow_mul]
  exact chunk_pow B2a hn

/-- B2: `2^60·224^r < 225^r` for `r ≥ 9600`. -/
theorem B2 {r : ℕ} (hr : 9600 ≤ r) : 2 ^ 60 * 224 ^ r < 225 ^ r := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h := B2b (n := 60) (by norm_num)
  rw [show 160 * 60 = 9600 by norm_num] at h
  rw [pow_add, pow_add]
  calc 2 ^ 60 * (224 ^ 9600 * 224 ^ j) = (2 ^ 60 * 224 ^ 9600) * 224 ^ j := by ring
    _ < 225 ^ 9600 * 225 ^ j :=
      Nat.mul_lt_mul_of_lt_of_le h (Nat.pow_le_pow_left (by norm_num) j) (by positivity)

/-- Base of B3 at `R₀ = 160·2^14 = 2621440`. -/
theorem B3base : 2 ^ 344 * 2621440 ^ 116 * 224 ^ 2621440 < 225 ^ 2621440 := by
  have h := B2b (n := 16384) (by norm_num)
  rw [show 160 * 16384 = 2621440 by norm_num] at h
  have h1 : 2621440 ^ 116 ≤ (2 ^ 22) ^ 116 := Nat.pow_le_pow_left (by norm_num) 116
  rw [← pow_mul] at h1
  have h2 : 2 ^ 344 * 2 ^ (22 * 116) ≤ 2 ^ 16384 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  calc 2 ^ 344 * 2621440 ^ 116 * 224 ^ 2621440 ≤ 2 ^ 344 * 2 ^ (22 * 116) * 224 ^ 2621440 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ ≤ 2 ^ 16384 * 224 ^ 2621440 := Nat.mul_le_mul_right _ h2
    _ < 225 ^ 2621440 := h

set_option exponentiation.threshold 1000 in
/-- B3: `2^344·r^116·224^r < 225^r` for `r ≥ 2621440`. -/
theorem B3 {r : ℕ} (hr : 2621440 ≤ r) : 2 ^ 344 * r ^ 116 * 224 ^ r < 225 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => exact B3base
  | succ L hL ih =>
    have h1 : (L+1)*30000 ≤ 30001*L := by omega
    have h2 : ((L+1)*30000)^116 ≤ (30001*L)^116 := Nat.pow_le_pow_left h1 116
    have h3 : 224 * 30001^116 ≤ 225 * 30000^116 := by norm_num
    have h4 : 224 * (L+1)^116 ≤ 225 * L^116 := by
      rw [mul_pow, mul_pow] at h2
      have hp : 0 < 30000^116 := by positivity
      have : 224 * (L+1)^116 * 30000^116 ≤ 225 * L^116 * 30000^116 := by
        calc 224 * (L+1)^116 * 30000^116 = 224 * ((L+1)^116 * 30000^116) := by ring
          _ ≤ 224 * (30001^116 * L^116) := Nat.mul_le_mul_left _ h2
          _ = (224 * 30001^116) * L^116 := by ring
          _ ≤ (225 * 30000^116) * L^116 := Nat.mul_le_mul_right _ h3
          _ = 225 * L^116 * 30000^116 := by ring
      exact Nat.le_of_mul_le_mul_right this hp
    calc 2^344 * (L+1)^116 * 224^(L+1) = 2^344 * (224 * (L+1)^116) * 224^L := by ring
      _ ≤ 2^344 * (225 * L^116) * 224^L := by gcongr
      _ = 225 * (2^344 * L^116 * 224^L) := by ring
      _ < 225 * 225^L := by omega
      _ = 225^(L+1) := by ring

/-- **Large-r size contradiction.** For `r ≥ 40901` (always true for a nontrivial
cycle, `NormCycleAll.cycle_params`), a Parseval bound `q^2 ≤ Q^r` (`q = 2^A - 3^r`) with
`Q ≤ 224/25 = 8.96` (case `2^A ≤ 2·3^r`) or `Q ≤ (896/225) θ^{2(A-r)}` (case `2^A > 2·3^r`)
is impossible. This raises the threshold `219/25` of `NormTwo.size_contra` (valid for
`r ≥ 2325`) to `224/25`. -/
theorem size_contra_big {r A : ℕ} {θ Q : ℝ} (hr : 40901 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A)
    (hAr : r ≤ A) (_hθ : 0 < θ) (hθr : θ ^ r = 2) (hQ0 : 0 ≤ Q)
    (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤ Q ^ r)
    (hii : 2 ^ A ≤ 2 * 3 ^ r → Q ≤ 224 / 25)
    (hi : 2 * 3 ^ r < 2 ^ A → Q ≤ 896 / 225 * θ ^ (2 * (A - r))) : False := by
  set q := 2 ^ A - 3 ^ r with hqdef
  have h3 : 3 ^ r < 2 ^ A := by omega
  by_cases hbig : 2 * 3 ^ r < 2 ^ A
  · have hQ' := hi hbig
    set X := θ ^ (2 * (A - r))
    have h2q : ((2 ^ A : ℕ) : ℝ) < 2 * q := by
      have : 2 ^ A < 2 * q := by omega
      exact_mod_cast this
    have hsq : ((2 ^ A : ℕ) : ℝ) ^ 2 < 4 * (q:ℝ) ^ 2 := by
      have := pow_lt_pow_left₀ h2q (by positivity) two_ne_zero
      nlinarith
    have hQr : Q ^ r ≤ (896 / 225 * X) ^ r := pow_le_pow_left₀ hQ0 hQ' r
    have hid : (896 / 225 * X) ^ r * 225 ^ r = 224 ^ r * ((2 ^ A : ℕ) : ℝ) ^ 2 := by
      rw [← fourX hθr hAr, ← mul_pow, ← mul_pow]; congr 1; ring
    have hpos : (0:ℝ) < (q:ℝ) ^ 2 := by
      have : 0 < q := by omega
      positivity
    have h75 : (0:ℝ) < 225 ^ r := by positivity
    have key : (q:ℝ) ^ 2 * 225 ^ r < 4 * 224 ^ r * (q:ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (hQ.trans hQr) h75.le
      rw [hid] at this
      nlinarith [pow_pos (show (0:ℝ) < 224 by norm_num) r]
    have hG := B1 (show 320 ≤ r by omega)
    have hG' : (4:ℝ) * 224 ^ r < 225 ^ r := by exact_mod_cast hG
    nlinarith
  · push Not at hbig
    have hQ' := hii hbig
    have kill : ∀ K : ℕ, 2 ^ A ≤ K * q → K ^ 2 * 224 ^ r < 225 ^ r → False := by
      intro K hgap hK
      have e1 : ((3 ^ r : ℕ) : ℝ) < ((2 ^ A : ℕ) : ℝ) := by exact_mod_cast h3
      have e2 : ((2 ^ A : ℕ) : ℝ) ≤ K * q := by exact_mod_cast hgap
      have e3 : ((3 ^ r : ℕ) : ℝ) ^ 2 < ((K:ℝ) * q) ^ 2 :=
        pow_lt_pow_left₀ (e1.trans_le e2) (by positivity) two_ne_zero
      have hQr : Q ^ r ≤ (224 / 25) ^ r := pow_le_pow_left₀ hQ0 hQ' r
      have e4 : ((K:ℝ) * q) ^ 2 ≤ (K:ℝ) ^ 2 * (224 / 25) ^ r := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hQ.trans hQr) (by positivity)
      have e5 : ((3 ^ r : ℕ) : ℝ) ^ 2 * 25 ^ r = 225 ^ r := by
        push_cast; rw [← pow_mul, mul_comm r 2, pow_mul, ← mul_pow]; norm_num
      have e6 : (K:ℝ) ^ 2 * (224 / 25) ^ r * 25 ^ r = (K:ℝ) ^ 2 * 224 ^ r := by
        rw [mul_assoc, ← mul_pow]; norm_num
      have hK' : (K:ℝ) ^ 2 * 224 ^ r < 225 ^ r := by exact_mod_cast hK
      have h25 : (0:ℝ) < 25 ^ r := by positivity
      nlinarith
    by_cases hmid : r < 225644606
    · exact kill (2 ^ 30) (gapBelow_225644606 r A (by omega) hmid h3) (by
        rw [← pow_mul]; exact B2 (by omega))
    · set_option exponentiation.threshold 400 in
      exact kill (2 ^ 172 * r ^ 58) (gap_all59 (k := r) (L := A) (by omega) h3) (by
        rw [mul_pow, ← pow_mul, ← pow_mul]; exact B3 (by omega))

/-- `θ^2 ≤ 1 + 3/40901` when `θ^r = 2`, `r ≥ 40901`. -/
theorem t_le_big {r : ℕ} {θ : ℝ} (hr : 40901 ≤ r) (hθ : 0 < θ) (hθr : θ ^ r = 2) :
    θ ^ 2 ≤ 1 + 3 / 40901 := by
  refine (theta_sq_le (by omega) hθ hθr).trans ?_
  have : (3:ℝ) / r ≤ 3 / 40901 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact_mod_cast hr
  linarith

end Collatz.NormBig

#print axioms Collatz.NormBig.B1
#print axioms Collatz.NormBig.B2
#print axioms Collatz.NormBig.B3
#print axioms Collatz.NormBig.size_contra_big
#print axioms Collatz.NormBig.t_le_big
