import NormSparse
import NormReduce
import FareyStretch
import CycleLenPoly59
import NormBridge

/-!
# two flips from the Christoffel word (DIRECTIVES 2(b))

Setting: `r ≥ 2325`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`, `A < 2r` (so `chr r A` has letters 1, 2
and `ρ := A mod r = A - r`); `q = 2^A - 3^r`, `g ∈ ZMod q` the unique element with `g^r = 2`,
`g^A = 3`, `G = g^((A-1)(r-1))` (Knight identity `(g-1) B(chr) = G`), `θ = 2^{1/r}`,
`X = θ^{2ρ}`.

* `no_cycle_two_left_flips` (T2): two down moves (partial sums lowered by one at two distinct
  down-sites). Reduction: `β = 1 - g + g^d - g^{d+1} + g^{e₁} = 0` (`e_i = ρ_i + 1`,
  `d = e₁ - e₂`; trinomial `1 - g^2 + g^{e₁}` when `d = 1`). This is the word-level, formal
  form of **Mghirbi's `E = 2`** case (known for actual cycles; credit Mghirbi).
* `no_cycle_two_right_flips` (T3): two up moves (partial sums raised by one at two distinct
  up-sites), provided one of them is off the "corner" (`3 p₁ ≤ r`, `p_i = r - 1 - ρ_i`).
  Reduction: `β' = 1 + (g-1)(g^{p₁} + g^{p₂}) = 0`. Plausibly new only in the large-defect-area
  regime: a right flip has Mghirbi defect area `E = p` exactly (checked at r = 401), and
  Mghirbi's coprime bound already covers `E ≤ 1.536 r^{2/3}`; Solomon does not treat right flips.
  The corner (both `p_i > r/3`) was left open here (`Q` can exceed 9) and is closed in `NormFlips`
  by `NormFlips.no_cycle_two_right_flips_all` (filtered engine).
* Both via `NormSparse.engine3/engine5` (`q^2 ≤ Q^r`, `Q = Σ θ^{2n}` over the support) and the
  size contradiction `size_contra` (`Q ≤ 219/25` when `2^A ≤ 2·3^r`, using the Farey gaps
  `gapBelow_225644606` / `gap_all59`; `Q ≤ (292/75) X` when `2^A > 2·3^r`).
* `cycle_two_left_flips`, `cycle_two_right_flips`: the same for actual positive `T`-cycles
  (via `NormBridge.cycle_word_eq`).

Limits (from numerics): no norm argument proves all of radius 2
(stacked moves and opposite-sign adjacent pairs have `|N| ≥ q`); the Parseval bound exceeds 9
for mixed up/down pairs, the up/up corner, and three down moves. Word-level for `r ≥ 2325`
only.
-/

namespace Collatz.NormTwo
open Collatz.NormGoal Collatz.NormReduce Collatz.NormSparse Finset


set_option exponentiation.threshold 3000 in
theorem G1 {r : ℕ} (hr : 2325 ≤ r) : 2 ^ 60 * 219 ^ r < 225 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r _ ih =>
    rw [pow_succ, pow_succ]
    calc 2 ^ 60 * (219 ^ r * 219) = (2 ^ 60 * 219 ^ r) * 219 := by ring
      _ < 225 ^ r * 219 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ 225 ^ r * 225 := Nat.mul_le_mul_left _ (by norm_num)

theorem G3 {r : ℕ} (hr : 60 ≤ r) : 4 * 73 ^ r < 75 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r _ ih => rw [pow_succ, pow_succ]; omega

set_option exponentiation.threshold 1000 in
theorem G2 {r : ℕ} (hr : 60000 ≤ r) : 2 ^ 344 * r ^ 116 * 219 ^ r < 225 ^ r := by
  induction r, hr using Nat.le_induction with
  | base =>
    set_option exponentiation.threshold 70000 in norm_num
  | succ L hL ih =>
    have h1 : (L+1)*5000 ≤ 5001*L := by omega
    have h2 : ((L+1)*5000)^116 ≤ (5001*L)^116 := Nat.pow_le_pow_left h1 116
    have h3 : 219 * 5001^116 ≤ 225 * 5000^116 := by norm_num
    have h4 : 219 * (L+1)^116 ≤ 225 * L^116 := by
      rw [mul_pow, mul_pow] at h2
      have hp : 0 < 5000^116 := by positivity
      have : 219 * (L+1)^116 * 5000^116 ≤ 225 * L^116 * 5000^116 := by
        calc 219 * (L+1)^116 * 5000^116 = 219 * ((L+1)^116 * 5000^116) := by ring
          _ ≤ 219 * (5001^116 * L^116) := Nat.mul_le_mul_left _ h2
          _ = (219 * 5001^116) * L^116 := by ring
          _ ≤ (225 * 5000^116) * L^116 := Nat.mul_le_mul_right _ h3
          _ = 225 * L^116 * 5000^116 := by ring
      exact Nat.le_of_mul_le_mul_right this hp
    calc 2^344 * (L+1)^116 * 219^(L+1) = 2^344 * (219 * (L+1)^116) * 219^L := by ring
      _ ≤ 2^344 * (225 * L^116) * 219^L := by gcongr
      _ = 225 * (2^344 * L^116 * 219^L) := by ring
      _ < 225 * 225^L := by omega
      _ = 225^(L+1) := by ring

section Size
variable {r A : ℕ} {θ : ℝ}

theorem theta_ge_one (hr : 0 < r) (hθ : 0 < θ) (hθr : θ ^ r = 2) : 1 ≤ θ := by
  by_contra h
  push Not at h
  have := pow_lt_one₀ hθ.le h (by omega : r ≠ 0)
  rw [hθr] at this; norm_num at this

theorem theta_pow_mono (hr : 0 < r) (hθ : 0 < θ) (hθr : θ ^ r = 2) {a b : ℕ} (hab : a ≤ b) :
    θ ^ (2 * a) ≤ θ ^ (2 * b) :=
  pow_le_pow_right₀ (theta_ge_one hr hθ hθr) (by omega)

theorem four_le_bern (hr : 0 < r) : (4:ℝ) ≤ (1 + 3 / r) ^ r := by
  have h0 : (0:ℝ) ≤ 3 / r := by positivity
  have := one_add_mul_le_pow (show (-2:ℝ) ≤ 3 / r by linarith) r
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [mul_div_cancel₀ _ hr'] at this
  linarith

/-- S1: `θ^2 ≤ 1 + 3/r`. -/
theorem theta_sq_le (hr : 0 < r) (hθ : 0 < θ) (hθr : θ ^ r = 2) : θ ^ 2 ≤ 1 + 3 / r := by
  have h : (θ ^ 2) ^ r ≤ (1 + 3 / r) ^ r := by
    rw [← pow_mul, mul_comm, pow_mul, hθr]; norm_num; exact four_le_bern hr
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp h

theorem fourX (hθr : θ ^ r = 2) (hAr : r ≤ A) :
    (4 * θ ^ (2 * (A - r))) ^ r = ((2 ^ A : ℕ) : ℝ) ^ 2 := by
  calc (4 * θ ^ (2 * (A - r))) ^ r = 4 ^ r * (θ ^ r) ^ (2 * (A - r)) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm r]
    _ = 2 ^ (2 * A) := by
        rw [hθr, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
    _ = ((2 ^ A : ℕ) : ℝ) ^ 2 := by push_cast; rw [← pow_mul, mul_comm]

/-- S2: in case `2^A ≤ 2·3^r`, `X ≤ (9/4)(1 + 3/r)`. -/
theorem X_le (hr : 0 < r) (hθ : 0 < θ) (hθr : θ ^ r = 2) (hAr : r ≤ A) (hii : 2 ^ A ≤ 2 * 3 ^ r) :
    θ ^ (2 * (A - r)) ≤ 9 / 4 * (1 + 3 / r) := by
  have h1 : ((2 ^ A : ℕ) : ℝ) ^ 2 ≤ 4 * (9:ℝ) ^ r := by
    have : ((2 ^ A : ℕ) : ℝ) ≤ 2 * (3:ℝ) ^ r := by exact_mod_cast hii
    calc ((2 ^ A : ℕ) : ℝ) ^ 2 ≤ (2 * (3:ℝ) ^ r) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = 4 * (9:ℝ) ^ r := by rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul]; norm_num
  have h2 : (4 * θ ^ (2 * (A - r))) ^ r ≤ (9 * (1 + 3 / r)) ^ r := by
    rw [fourX hθr hAr, mul_pow]
    nlinarith [four_le_bern hr, pow_pos (show (0:ℝ) < 9 by norm_num) r]
  have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp h2
  linarith

/-- S3: in case `2·3^r < 2^A`, `X ≥ 9/4`. -/
theorem X_ge (hr : 0 < r) (hθ : 0 < θ) (hθr : θ ^ r = 2) (hAr : r ≤ A) (hi : 2 * 3 ^ r < 2 ^ A) :
    9 / 4 ≤ θ ^ (2 * (A - r)) := by
  have h1 : (9:ℝ) ^ r < (4 * θ ^ (2 * (A - r))) ^ r := by
    rw [fourX hθr hAr]
    have : 2 * (3:ℝ) ^ r < ((2 ^ A : ℕ) : ℝ) := by exact_mod_cast hi
    have h3 : (2 * (3:ℝ) ^ r) ^ 2 < ((2 ^ A : ℕ) : ℝ) ^ 2 :=
      pow_lt_pow_left₀ this (by positivity) two_ne_zero
    have : (2 * (3:ℝ) ^ r) ^ 2 = 4 * 9 ^ r := by
      rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul]; norm_num
    nlinarith [pow_pos (show (0:ℝ) < 9 by norm_num) r]
  have := (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp h1
  linarith

/-- S4: if `3p ≤ r` then `θ^{2p} ≤ 8/5`. -/
theorem Y_le (hr : 0 < r) (hθ : 0 < θ) (hθr : θ ^ r = 2) {p : ℕ} (hp : 3 * p ≤ r) :
    θ ^ (2 * p) ≤ 8 / 5 := by
  have h1 : ((θ ^ (2 * p)) ^ 3) ^ r ≤ ((4:ℝ)) ^ r := by
    rw [← pow_mul, ← pow_mul, show 2 * p * (3 * r) = r * (6 * p) by ring, pow_mul, hθr,
      show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 := (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by omega)).mp h1
  by_contra h
  push Not at h
  have : (8/5:ℝ) ^ 3 < (θ ^ (2 * p)) ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  norm_num at this; linarith

/-- The size contradiction: a Parseval bound `q^2 ≤ Q^r` with `Q ≤ 219/25` (case
`2^A ≤ 2·3^r`) or `Q ≤ (292/75) θ^{2(A-r)}` (case `2^A > 2·3^r`) is impossible for
`r ≥ 2325`. -/
theorem size_contra (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hAr : r ≤ A) {Q : ℝ}
    (hθ : 0 < θ) (hθr : θ ^ r = 2) (hQ0 : 0 ≤ Q) (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤ Q ^ r)
    (hii : 2 ^ A ≤ 2 * 3 ^ r → Q ≤ 219 / 25)
    (hi : 2 * 3 ^ r < 2 ^ A → Q ≤ 292 / 75 * θ ^ (2 * (A - r))) : False := by
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
    have hQr : Q ^ r ≤ (292 / 75 * X) ^ r := pow_le_pow_left₀ hQ0 hQ' r
    have hid : (292 / 75 * X) ^ r * 75 ^ r = 73 ^ r * ((2 ^ A : ℕ) : ℝ) ^ 2 := by
      rw [← fourX hθr hAr, ← mul_pow, ← mul_pow]; congr 1; ring
    have hpos : (0:ℝ) < (q:ℝ) ^ 2 := by
      have : 0 < q := by omega
      positivity
    have h75 : (0:ℝ) < 75 ^ r := by positivity
    have key : (q:ℝ) ^ 2 * 75 ^ r < 4 * 73 ^ r * (q:ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (hQ.trans hQr) h75.le
      rw [hid] at this
      nlinarith [pow_pos (show (0:ℝ) < 73 by norm_num) r]
    have hG := G3 (show 60 ≤ r by omega)
    have hG' : (4:ℝ) * 73 ^ r < 75 ^ r := by exact_mod_cast hG
    nlinarith
  · push Not at hbig
    have hQ' := hii hbig
    have kill : ∀ K : ℕ, 2 ^ A ≤ K * q → K ^ 2 * 219 ^ r < 225 ^ r → False := by
      intro K hgap hK
      have e1 : ((3 ^ r : ℕ) : ℝ) < ((2 ^ A : ℕ) : ℝ) := by exact_mod_cast h3
      have e2 : ((2 ^ A : ℕ) : ℝ) ≤ K * q := by exact_mod_cast hgap
      have e3 : ((3 ^ r : ℕ) : ℝ) ^ 2 < ((K:ℝ) * q) ^ 2 :=
        pow_lt_pow_left₀ (e1.trans_le e2) (by positivity) two_ne_zero
      have hQr : Q ^ r ≤ (219 / 25) ^ r := pow_le_pow_left₀ hQ0 hQ' r
      have e4 : ((K:ℝ) * q) ^ 2 ≤ (K:ℝ) ^ 2 * (219 / 25) ^ r := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hQ.trans hQr) (by positivity)
      have e5 : ((3 ^ r : ℕ) : ℝ) ^ 2 * 25 ^ r = 225 ^ r := by
        push_cast; rw [← pow_mul, mul_comm r 2, pow_mul, ← mul_pow]; norm_num
      have e6 : (K:ℝ) ^ 2 * (219 / 25) ^ r * 25 ^ r = (K:ℝ) ^ 2 * 219 ^ r := by
        rw [mul_assoc, ← mul_pow]; norm_num
      have hK' : (K:ℝ) ^ 2 * 219 ^ r < 225 ^ r := by exact_mod_cast hK
      have h25 : (0:ℝ) < 25 ^ r := by positivity
      nlinarith
    by_cases hmid : r < 225644606
    · exact kill (2 ^ 30) (gapBelow_225644606 r A (by omega) hmid h3) (by
        rw [← pow_mul]; exact G1 hr)
    · set_option exponentiation.threshold 400 in
      exact kill (2 ^ 172 * r ^ 58) (gap_all59 (k := r) (L := A) (by omega) h3) (by
        rw [mul_pow, ← pow_mul, ← pow_mul]; exact G2 (by omega))

end Size

section Finish
variable {r A : ℕ} {θ : ℝ}

theorem eps_le (hr : 2325 ≤ r) : (3:ℝ) / r ≤ 3 / 2325 := by
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  exact_mod_cast hr

/-- Size finish for two left flips: `Q ≤ 1 + θ^2 + 3X`. -/
theorem finish_left (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hAr : r ≤ A) {Q : ℝ}
    (hθ : 0 < θ) (hθr : θ ^ r = 2) (hQ0 : 0 ≤ Q) (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤ Q ^ r)
    (hQle : Q ≤ 1 + θ ^ 2 + 3 * θ ^ (2 * (A - r))) : False := by
  have hr0 : 0 < r := by omega
  have hε := eps_le hr
  have hε0 : (0:ℝ) ≤ 3 / r := by positivity
  have ht := theta_sq_le hr0 hθ hθr
  refine size_contra hr hq hAr hθ hθr hQ0 hQ (fun hii => ?_) (fun hi => ?_)
  · have hX := X_le hr0 hθ hθr hAr hii
    linarith
  · have hX := X_ge hr0 hθ hθr hAr hi
    linarith

/-- Size finish for two right flips: `Q ≤ 1 + (1 + θ^2)(8/5 + X)`. -/
theorem finish_right (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hAr : r ≤ A) {Q : ℝ}
    (hθ : 0 < θ) (hθr : θ ^ r = 2) (hQ0 : 0 ≤ Q) (hQ : (((2 ^ A - 3 ^ r : ℕ)) : ℝ) ^ 2 ≤ Q ^ r)
    (hQle : Q ≤ 1 + (1 + θ ^ 2) * (8 / 5 + θ ^ (2 * (A - r)))) : False := by
  have hr0 : 0 < r := by omega
  have hε := eps_le hr
  have hε0 : (0:ℝ) ≤ 3 / r := by positivity
  have ht := theta_sq_le hr0 hθ hθr
  have hX0 : (0:ℝ) ≤ θ ^ (2 * (A - r)) := by positivity
  have ht0 : (0:ℝ) ≤ θ ^ 2 := by positivity
  have h1 : (1 + θ ^ 2) * (8 / 5 + θ ^ (2 * (A - r))) ≤
      (2 + 3 / r) * (8 / 5 + θ ^ (2 * (A - r))) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  refine size_contra hr hq hAr hθ hθr hQ0 hQ (fun hii => ?_) (fun hi => ?_)
  · have hX := X_le hr0 hθ hθr hAr hii
    have h2 : (2 + 3 / r) * (8 / 5 + θ ^ (2 * (A - r))) ≤
        (2 + 3 / r) * (8 / 5 + 9 / 4 * (1 + 3 / r)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  · have hX := X_ge hr0 hθ hθr hAr hi
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) (show (0:ℝ) ≤ 3 / 2325 - 3 / r by linarith)]

end Finish

section Core
variable {r A : ℕ}

/-- Core of two left flips: from `2G = (g-1)(G g^(r-1-ρ₁) + G g^(r-1-ρ₂))` with
`1 ≤ ρ₂ < ρ₁ < A - r`, contradiction. -/
theorem core_left (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r)
    {g G : ZMod (2 ^ A - 3 ^ r)} (h2 : g ^ r = 2) (hGu : IsUnit G)
    {ρ₁ ρ₂ : ℕ} (h12 : ρ₂ < ρ₁) (hρ2 : 1 ≤ ρ₂) (hρ1 : ρ₁ < A - r)
    (heq : 2 * G = (g - 1) * (G * g ^ (r - 1 - ρ₁) + G * g ^ (r - 1 - ρ₂))) : False := by
  have hAr : r < A := r_lt_A hq
  have hgu := isUnit_g (by omega) hq h2
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  set d := ρ₁ - ρ₂ with hd
  have hp1 : g ^ r = g ^ (r - 1 - ρ₁) * g ^ (ρ₁ + 1) := by rw [← pow_add]; congr 1; omega
  have hb : g ^ (r - 1 - ρ₂) = g ^ (r - 1 - ρ₁) * g ^ d := by rw [← pow_add]; congr 1; omega
  have hβ0 : (G * g ^ (r - 1 - ρ₁)) * (1 - g + g ^ d - g ^ d * g + g ^ (ρ₁ + 1)) = 0 := by
    linear_combination heq - G * hp1 + G * h2 + (g - 1) * G * hb
  have hβ := (hGu.mul (hgu.pow _)).mul_right_eq_zero.mp hβ0
  obtain ⟨θ, hθ, hθr⟩ := exists_theta (show 0 < r by omega)
  have hr0 : 0 < r := by omega
  have mono := fun {a b : ℕ} (h : a ≤ b) => theta_pow_mono hr0 hθ hθr h
  have hX0 : (0:ℝ) ≤ θ ^ (2 * (A - r)) := by positivity
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · have hd1' : d = 1 := by omega
    rw [hd1', pow_one] at hβ
    have h3t : 1 - g ^ 2 + g ^ (ρ₁ + 1) = 0 := by linear_combination hβ
    have hE := engine3 hq1 (by norm_num) (by omega) (by omega) (by omega) (by omega) g h2 h3t θ hθ hθr
    refine finish_left hr hq hAr.le hθ hθr (by positivity) hE ?_
    have := mono (show 2 ≤ A - r by omega)
    have := mono (show ρ₁ + 1 ≤ A - r by omega)
    nlinarith [sq_nonneg θ]
  · have h5 : 1 - g ^ 1 + g ^ d - g ^ (d + 1) + g ^ (ρ₁ + 1) = 0 := by
      rw [pow_one, pow_succ g d]; exact hβ
    have hE := engine5 hq1 (by norm_num) (by omega) (by omega) (by omega) (by omega) g h2 h5 θ hθ hθr
    refine finish_left hr hq hAr.le hθ hθr (by positivity) hE ?_
    have := mono (show d ≤ A - r by omega)
    have := mono (show d + 1 ≤ A - r by omega)
    have := mono (show ρ₁ + 1 ≤ A - r by omega)
    simp only [mul_one]
    linarith

/-- Core of two right flips: from `G + (g-1)(G g^a + G g^b) = 0` with `a < b`, `3a ≤ r`,
`b + 1 ≤ A - r`, contradiction. -/
theorem core_right (hr : 2325 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r)
    {g G : ZMod (2 ^ A - 3 ^ r)} (h2 : g ^ r = 2) (hGu : IsUnit G)
    {a b : ℕ} (hab : a < b) (ha3 : 3 * a ≤ r) (hbA : b + 1 ≤ A - r)
    (heq : G + (g - 1) * (G * g ^ a + G * g ^ b) = 0) : False := by
  have := nontrivial_q hq
  have hAr : r < A := r_lt_A hq
  have hgu := isUnit_g (by omega) hq h2
  have hq1 : 1 < 2 ^ A - 3 ^ r := by omega
  have hr0 : 0 < r := by omega
  obtain ⟨θ, hθ, hθr⟩ := exists_theta hr0
  have mono := fun {a b : ℕ} (h : a ≤ b) => theta_pow_mono hr0 hθ hθr h
  have hX0 : (0:ℝ) ≤ θ ^ (2 * (A - r)) := by positivity
  have hθ1 := theta_ge_one hr0 hθ hθr
  have ht1 : (1:ℝ) ≤ θ ^ 2 := one_le_pow₀ hθ1
  have hβ : 1 + (g - 1) * (g ^ a + g ^ b) = 0 := by
    have := hGu.mul_right_eq_zero.mp (show G * (1 + (g - 1) * (g ^ a + g ^ b)) = 0 by
      linear_combination heq)
    exact this
  rcases Nat.eq_zero_or_pos a with ha0 | ha1
  · subst ha0
    rcases Nat.lt_or_ge b 2 with hb1 | hb2
    · have hb1' : b = 1 := by omega
      subst hb1'
      have : g ^ 2 = 0 := by linear_combination hβ
      exact (hgu.pow 2).ne_zero this
    · have hsplit : g ^ b = g ^ (b - 1) * g := by rw [← pow_succ]; congr 1; omega
      have h0 : g * (1 - g ^ (b - 1) + g ^ b) = 0 := by
        linear_combination hβ + hsplit
      have h3t := hgu.mul_right_eq_zero.mp h0
      have hE := engine3 hq1 (by omega) (by omega) (by omega) (by omega) (by omega) g h2 h3t θ hθ hθr
      refine finish_right hr hq hAr.le hθ hθr (by positivity) hE ?_
      have := mono (show b - 1 ≤ A - r by omega)
      have := mono (show b ≤ A - r by omega)
      nlinarith
  · rcases Nat.lt_or_ge (a + 1) b with hgen | hadj
    · have h5 : 1 - g ^ a + g ^ (a + 1) - g ^ b + g ^ (b + 1) = 0 := by
        rw [pow_succ, pow_succ]; linear_combination hβ
      have hE := engine5 hq1 ha1 (by omega) hgen (by omega) (by omega) g h2 h5 θ hθ hθr
      refine finish_right hr hq hAr.le hθ hθr (by positivity) hE ?_
      have hY := Y_le hr0 hθ hθr ha3
      have := mono (show b ≤ A - r by omega)
      have e1 : θ ^ (2 * (a + 1)) = θ ^ 2 * θ ^ (2 * a) := by rw [← pow_add]; congr 1; ring
      have e2 : θ ^ (2 * (b + 1)) = θ ^ 2 * θ ^ (2 * b) := by rw [← pow_add]; congr 1; ring
      rw [e1, e2]
      have : (1 + θ ^ 2) * (θ ^ (2 * a) + θ ^ (2 * b)) ≤ (1 + θ ^ 2) * (8 / 5 + θ ^ (2 * (A - r))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    · have hb' : b = a + 1 := by omega
      subst hb'
      have h3t : 1 - g ^ a + g ^ (a + 2) = 0 := by
        rw [show g ^ (a + 2) = g ^ a * g * g by ring]; linear_combination hβ
      have hE := engine3 hq1 ha1 (by omega) (by omega) (by omega) (by omega) g h2 h3t θ hθ hθr
      refine finish_right hr hq hAr.le hθ hθr (by positivity) hE ?_
      have hY := Y_le hr0 hθ hθr ha3
      have := mono (show a + 2 ≤ A - r by omega)
      nlinarith

end Core

section Main

theorem sum_two_pt {R : Type*} [AddCommMonoid R] {s : Finset ℕ} (F : ℕ → R) {k₁ k₂ : ℕ}
    (h1 : k₁ ∈ s) (h2 : k₂ ∈ s) :
    ∑ i ∈ s, (F i + (if i = k₁ then F i else 0) + (if i = k₂ then F i else 0)) =
      ∑ i ∈ s, F i + F k₁ + F k₂ := by
  simp [sum_add_distrib, h1, h2]

theorem modA {r A : ℕ} (hAr : r < A) (hA : A < 2 * r) : A % r = A - r := by
  have h1 : A / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have := Nat.div_add_mod A r
  rw [h1] at this; omega

/-- **Two left flips (word-level form of Mghirbi's `E = 2`).** Let `r ≥ 2325`,
`gcd(A, r) = 1`, `3^r + 1 < 2^A`, `A < 2r`. If the partial sums of `v` equal those of the
Christoffel word `chr r A` minus one at two distinct down-sites `k₁ ≠ k₂` in `(0, r)`
(`k A mod r < A mod r`, i.e. `chr (k-1) = 2`; lowering `A_k` by one = moving one unit of
valuation from position `k-1` to position `k`), and agree elsewhere below `r`, then
`(2^A - 3^r) ∤ B(v)`. -/
theorem no_cycle_two_left_flips (r A : ℕ) (hr : 2325 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r) (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r)
    (h2' : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : k₁ * A % r < A % r) (hs2 : k₂ * A % r < A % r)
    (v : ℕ → ℕ) (hv : ∀ i < r, psum v i + (if i = k₁ ∨ i = k₂ then 1 else 0) = psum (NormGoal.chr r A) i) :
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
  have hpt : ∀ i ∈ range r, Fw i = Fv i + (if i = k₁ then Fv i else 0) +
      (if i = k₂ then Fv i else 0) := by
    intro i hi
    have hi' := mem_range.mp hi
    have hvi := hv i hi'
    by_cases e1 : i = k₁
    · have e2 : ¬ i = k₂ := by omega
      rw [if_pos (Or.inl e1)] at hvi
      have hp : psum (NormGoal.chr r A) i = psum v i + 1 := by omega
      simp only [hFv, hFw]; rw [hp, if_pos e1, if_neg e2, pow_succ]; ring
    · by_cases e2 : i = k₂
      · rw [if_pos (Or.inr e2)] at hvi
        have hp : psum (NormGoal.chr r A) i = psum v i + 1 := by omega
        simp only [hFv, hFw]; rw [hp, if_neg e1, if_pos e2, pow_succ]; ring
      · rw [if_neg (by tauto)] at hvi
        have hp : psum (NormGoal.chr r A) i = psum v i := by omega
        simp only [hFv, hFw]; rw [hp, if_neg e1, if_neg e2]; ring
  have hsum : (Bnum r (NormGoal.chr r A) : ZMod (2 ^ A - 3 ^ r)) = ∑ i ∈ range r, Fv i + Fv k₁ + Fv k₂ := by
    rw [hBw, ← sum_two_pt Fv (mem_range.mpr h1r) (mem_range.mpr h2r)]
    exact sum_congr rfl hpt
  have hF : ∀ k, k < r → (k = k₁ ∨ k = k₂) → 2 * Fv k = G * g ^ (r - 1 - k * A % r) := by
    intro k hk hk12
    have hvk := hv k hk
    rw [if_pos hk12] at hvk
    rw [← term_chr h2 h3 hA1 hk, ← hvk, pow_succ]
    simp only [hFv]; ring
  have hF1 := hF k₁ h1r (Or.inl rfl)
  have hF2 := hF k₂ h2r (Or.inr rfl)
  have hsv : ∑ i ∈ range r, Fv i = 0 := hBv
  rw [hsv, zero_add] at hsum
  have heq : 2 * G = (g - 1) * (G * g ^ (r - 1 - k₁ * A % r) + G * g ^ (r - 1 - k₂ * A % r)) := by
    linear_combination (-2:ZMod (2 ^ A - 3 ^ r)) * hK + 2 * (g - 1) * hsum + (g - 1) * (hF1 + hF2)
  have hρne : k₁ * A % r ≠ k₂ * A % r := fun h => hne (mod_inj hcop h1r h2r h)
  have hpos : ∀ k, 0 < k → k < r → 1 ≤ k * A % r := by
    intro k hk hkr
    by_contra h0
    have : k * A % r = 0 * A % r := by simp; omega
    have := mod_inj hcop hkr (by omega) this
    omega
  rcases Nat.lt_or_gt_of_ne hρne with hlt | hgt
  · exact core_left hr hq hA h2 hGu hlt (hpos k₁ h1 h1r) (by omega) (by rw [heq]; ring)
  · exact core_left hr hq hA h2 hGu hgt (hpos k₂ h2' h2r) (by omega) heq

/-- **Two right flips off the corner (plausibly new only for large defect area
`E = p`, beyond Mghirbi's `E ≤ 1.536 r^{2/3}`; superseded by
`NormFlips.no_cycle_two_right_flips_all`).** Let `r ≥ 2325`,
`gcd(A, r) = 1`, `3^r + 1 < 2^A`, `A < 2r`. If the partial sums of `v` equal those of
`chr r A` plus one at two distinct up-sites `k₁ ≠ k₂` in `(0, r)` (`r ≤ k A mod r + A mod r`,
i.e. `chr k = 2`; raising `A_k` by one = moving one unit from position `k` to `k-1`), agree
elsewhere below `r`, and the flip at `k₁` is off the corner (`3 (r - 1 - k₁ A mod r) ≤ r`),
then `(2^A - 3^r) ∤ B(v)`. -/
theorem no_cycle_two_right_flips (r A : ℕ) (hr : 2325 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hA : A < 2 * r) (k₁ k₂ : ℕ) (_h1 : 0 < k₁) (h1r : k₁ < r)
    (_h2' : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : r ≤ k₁ * A % r + A % r) (hs2 : r ≤ k₂ * A % r + A % r)
    (hcorner : 3 * (r - 1 - k₁ * A % r) ≤ r)
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
  · exact core_right hr hq hA h2 hGu hlt hcorner (by omega) heq
  · exact core_right hr hq hA h2 hGu hgt (by omega) (by omega) (by rw [← heq]; ring)

end Main

section Cycle
open CollatzProof

theorem cycle_q {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hv1 : ∀ i < r, 1 ≤ v i)
    (hL : psum v r = L) (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j))
    (hcyc : T^[L] m = m) : 3 ^ r + 1 < 2 ^ L ∧ (2 ^ L - 3 ^ r) ∣ Bnum r v := by
  have heq := NormBridge.cycle_word_eq hv1 hL hodd hcyc
  have hBpos : 0 < Bnum r v := by
    unfold Bnum
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr (by omega), by positivity⟩
  have hlt : 3 ^ r < 2 ^ L := by
    by_contra h
    rw [Nat.sub_eq_zero_of_le (not_lt.mp h), zero_mul] at heq; omega
  refine ⟨?_, ⟨m, by rw [← heq, mul_comm]⟩⟩
  by_contra h
  have := NormAll.pow_two_eq_three_pow_succ (a := L) (b := r) (by omega) (by omega)
  omega

/-- **Cycle form of T2.** No positive `T`-cycle (period `L`, `r ≥ 2325` odd steps,
`gcd(L, r) = 1`, `L < 2r`) has a valuation word that is two left flips (at down-sites) from
the Christoffel word `chr r L`. -/
theorem cycle_two_left_flips {m L r : ℕ} {v : ℕ → ℕ} (hr : 2325 ≤ r) (hcop : Nat.Coprime L r)
    (hL2 : L < 2 * r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : k₁ * L % r < L % r) (hs2 : k₂ * L % r < L % r)
    (hv : ∀ i < r, psum v i + (if i = k₁ ∨ i = k₂ then 1 else 0) = psum (NormGoal.chr r L) i) : False := by
  obtain ⟨hq, hdiv⟩ := cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_two_left_flips r L hr hcop hq hL2 k₁ k₂ h1 h1r h2 h2r hne hs1 hs2 v hv hdiv

/-- **Cycle form of T3.** No positive `T`-cycle (period `L`, `r ≥ 2325` odd steps,
`gcd(L, r) = 1`, `L < 2r`) has a valuation word that is two right flips (at up-sites, one of
them off the corner) from the Christoffel word `chr r L`. -/
theorem cycle_two_right_flips {m L r : ℕ} {v : ℕ → ℕ} (hr : 2325 ≤ r) (hcop : Nat.Coprime L r)
    (hL2 : L < 2 * r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h1r : k₁ < r) (h2 : 0 < k₂) (h2r : k₂ < r) (hne : k₁ ≠ k₂)
    (hs1 : r ≤ k₁ * L % r + L % r) (hs2 : r ≤ k₂ * L % r + L % r)
    (hcorner : 3 * (r - 1 - k₁ * L % r) ≤ r)
    (hv : ∀ i < r, psum v i = psum (NormGoal.chr r L) i + (if i = k₁ ∨ i = k₂ then 1 else 0)) : False := by
  obtain ⟨hq, hdiv⟩ := cycle_q (by omega) hv1 hL hodd hcyc
  exact no_cycle_two_right_flips r L hr hcop hq hL2 k₁ k₂ h1 h1r h2 h2r hne hs1 hs2 hcorner v hv hdiv

end Cycle

end Collatz.NormTwo

#print axioms Collatz.NormTwo.size_contra
#print axioms Collatz.NormTwo.no_cycle_two_left_flips
#print axioms Collatz.NormTwo.no_cycle_two_right_flips
#print axioms Collatz.NormTwo.cycle_two_left_flips
#print axioms Collatz.NormTwo.cycle_two_right_flips
