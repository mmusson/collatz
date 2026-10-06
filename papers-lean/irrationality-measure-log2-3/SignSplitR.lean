import SignSplit

/-!
# Rational-rate sign-split transference

`SignApproxR a b cQ cE cL e d Q P1 P2` generalizes `SignApprox a b c d`: the decay factor is
`2^{⌊e m/d⌋}` and the three constants (size of `Q`, error bound, lower bound) are separate.
The mechanism is the same sign split as in `SignSplit.lean`; only the index choice
`m = d·⌊(k0+e)/e⌋` changes, so that `⌊e m/d⌋ = e j ∈ [k0+1, k0+e]`.
* `linForm_lower_of_signApproxR`: `(a+b)d ≤ e r` ⇒
  `1 ≤ 2^{cQ+cL+5} (2^{cE+1+e}(p+q))^r |q log 3 − p log 2|`.
* `irrMeasHyp_of_signApproxR`: moreover `2^{cQ+cL+5+(cE+3+e)r} ≤ Q0^t`, `t ≥ 1`, `Q0 ≥ 3` ⇒
  `IrrMeasHyp (r+1+t) Q0`.
-/

namespace Collatz

/-- Rational-rate sign-split approximation data for `(log(4/3), log(9/8))` (hypothesis
interface, a definition): for every `m`, `|Q_m| ≤ 2^{cQ+am}`;
`|E_j(m)|·2^{⌊e m/d⌋} ≤ 2^{cE}`; `E1 ≤ 0 ≤ E2`; `1 ≤ |E1|·2^{cL+bm}`, where
`E1 = Q_m log(4/3) − P1_m`, `E2 = Q_m log(9/8) − P2_m`. -/
def SignApproxR (a b cQ cE cL e d : ℕ) (Q P1 P2 : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, |(Q m : ℝ)| ≤ 2^(cQ + a*m) ∧
    |(Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m| * 2^((e*m)/d) ≤ 2^cE ∧
    |(Q m : ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2 m| * 2^((e*m)/d) ≤ 2^cE ∧
    (Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m ≤ 0 ∧
    0 ≤ (Q m : ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2 m ∧
    1 ≤ |(Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m| * 2^(cL + b*m)

/-- The old interface is the special case `e = 1`, `cQ = cE = cL = c`. -/
theorem signApproxR_of_signApprox {a b c d : ℕ} {Q P1 P2 : ℕ → ℤ}
    (h : SignApprox a b c d Q P1 P2) : SignApproxR a b c c c 1 d Q P1 P2 := by
  intro m
  simpa only [one_mul] using h m

/-- Lower bound for `|q log 3 − p log 2|` from `SignApproxR` (unconditional implication):
if `d, e ≥ 1`, `(a+b)d ≤ e r` and `q ≥ 1`, then
`1 ≤ 2^{cQ+cL+5}(2^{cE+1+e}(p+q))^r |q log 3 − p log 2|`. -/
theorem linForm_lower_of_signApproxR {a b cQ cE cL e d r : ℕ} {Q P1 P2 : ℕ → ℤ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (hr : (a+b)*d ≤ e*r)
    (h : SignApproxR a b cQ cE cL e d Q P1 P2) (p q : ℕ) (hq : 1 ≤ q) :
    1 ≤ (2:ℝ)^(cQ+cL+5) * ((2:ℝ)^(cE+1+e) * (p+q))^r *
      |(q:ℝ) * Real.log 3 - p * Real.log 2| := by
  set Λ : ℝ := (q:ℝ) * Real.log 3 - p * Real.log 2 with hΛ
  have hM1 := log_four_thirds_ge
  have hM2 := log_nine_eighths_ge
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have hY1 : (1:ℝ) ≤ (2:ℝ)^(cE+1+e) * (p+q) := by
    have : (1:ℝ) ≤ 2^(cE+1+e) := one_le_pow₀ (by norm_num)
    nlinarith
  have hYe : (1:ℝ) ≤ ((2:ℝ)^(cE+1+e) * (p+q))^r := one_le_pow₀ hY1
  have h2c : (32:ℝ) ≤ 2^(cQ+cL+5) := by
    calc (32:ℝ) = 2^5 := by norm_num
      _ ≤ 2^(cQ+cL+5) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hΛ0 := abs_nonneg Λ
  have easy : (1:ℝ)/18 ≤ |Λ| →
      1 ≤ 2^(cQ+cL+5) * ((2:ℝ)^(cE+1+e) * (p+q))^r * |Λ| := by
    intro hl
    have : (32:ℝ) * 1 * (1/18) ≤ 2^(cQ+cL+5) * ((2:ℝ)^(cE+1+e) * (p+q))^r * |Λ| :=
      mul_le_mul (mul_le_mul h2c hYe (by norm_num) (by positivity)) hl (by norm_num)
        (by positivity)
    linarith
  rcases le_or_gt (2*p) (3*q) with h1 | h1
  · apply easy
    have h1r : (2:ℝ)*p ≤ 3*q := by exact_mod_cast h1
    have hΛid : Λ = (q/2) * (2*Real.log 3 - 3*Real.log 2) + (3*q - 2*p)/2 * Real.log 2 := by
      rw [hΛ]; ring
    have hm2 := mul_le_mul hqr hM2 (by norm_num) (by linarith)
    have hl := mul_nonneg (show (0:ℝ) ≤ (3*q - 2*p)/2 by linarith) l2.le
    have : (1:ℝ)/18 ≤ Λ := by
      rw [hΛid]; linarith
    exact le_trans this (le_abs_self _)
  rcases le_or_gt (2*q) p with h2 | h2
  · apply easy
    have h2r : (2:ℝ)*q ≤ p := by exact_mod_cast h2
    have hΛid : -Λ = q * (2*Real.log 2 - Real.log 3) + (p - 2*q) * Real.log 2 := by
      rw [hΛ]; ring
    have hm1 := mul_le_mul hqr hM1 (by norm_num) (by linarith)
    have hl := mul_nonneg (show (0:ℝ) ≤ p - 2*q by linarith) l2.le
    have : (1:ℝ)/18 ≤ -Λ := by rw [hΛid]; linarith
    exact le_trans this (neg_le_abs _)
  -- main case: 3q < 2p, p < 2q
  have h1r : (3:ℝ)*q + 1 ≤ 2*p := by exact_mod_cast h1
  have h2r : (p:ℝ) + 1 ≤ 2*q := by exact_mod_cast h2
  set X : ℕ := 2^(cE+1) * (p+q) with hXdef
  have hX0 : X ≠ 0 := by positivity
  set k0 := Nat.log 2 X with hk
  have hXlt : X < 2^(k0+1) := Nat.lt_pow_succ_log_self (by norm_num) X
  have hXge : 2^k0 ≤ X := Nat.pow_log_le_self 2 hX0
  set j := (k0 + e) / e with hj
  have hj1 : k0 + 1 ≤ e * j := by
    have := Nat.div_add_mod (k0+e) e
    have := Nat.mod_lt (k0+e) (show 0 < e by omega)
    rw [hj]; nlinarith
  have hj2 : e * j ≤ k0 + e := by rw [hj]; exact Nat.mul_div_le (k0+e) e
  set m := d * j with hm
  have hmd : (e*m) / d = e*j := by
    rw [hm, show e*(d*j) = d*(e*j) by ring]
    exact Nat.mul_div_cancel_left (e*j) (by omega)
  obtain ⟨hQ, hE1, hE2, hs1, hs2, hlow⟩ := h m
  rw [hmd] at hE1 hE2
  set E1 := (Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m with hE1def
  set E2 := (Q m : ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2 m with hE2def
  set A : ℝ := 3*q - 2*p with hA
  set B : ℝ := 2*q - p with hB
  set N : ℤ := (3*q - 2*p : ℤ) * P1 m + (2*q - p : ℤ) * P2 m with hN
  have hid : (Q m : ℝ) * Λ = N + A*E1 + B*E2 := by
    rw [hN, hA, hB, hE1def, hE2def, hΛ]; push_cast; ring
  have hK : (0:ℝ) < 2^(e*j) := by positivity
  have hXr : (2:ℝ)^(cE+1) * (p+q) < 2^(e*j) := by
    have h' : X < 2^(e*j) := lt_of_lt_of_le hXlt (Nat.pow_le_pow_right (by norm_num) hj1)
    have : ((2^(cE+1) * (p+q) : ℕ) : ℝ) < ((2^(e*j) : ℕ) : ℝ) := by exact_mod_cast h'
    push_cast at this; exact this
  have habs1 : |E1| = -E1 := abs_of_nonpos hs1
  have habs2 : |E2| = E2 := abs_of_nonneg hs2
  rw [habs1] at hE1 hlow
  rw [habs2] at hE2
  have hA' : 0 ≤ -A := by rw [hA]; linarith
  have hB' : 0 ≤ B := by rw [hB]; linarith
  have hS : (A*E1 + B*E2) * 2^(e*j) ≤ (p+q) * 2^cE := by
    have ee : (A*E1 + B*E2) * 2^(e*j) = (-A) * ((-E1) * 2^(e*j)) + B * (E2 * 2^(e*j)) := by
      ring
    rw [ee]
    have h2c0 : (0:ℝ) < 2^cE := by positivity
    calc _ ≤ (-A) * 2^cE + B * 2^cE :=
          add_le_add (mul_le_mul_of_nonneg_left hE1 hA') (mul_le_mul_of_nonneg_left hE2 hB')
      _ = (p - q) * 2^cE := by rw [hA, hB]; ring
      _ ≤ (p+q) * 2^cE := mul_le_mul_of_nonneg_right (by linarith) h2c0.le
  have hS2 : A*E1 + B*E2 < 1/2 := by
    have ee : (2:ℝ)^(cE+1) = 2 * 2^cE := by ring
    rw [ee] at hXr
    have : (A*E1 + B*E2) * 2^(e*j) < (1/2) * 2^(e*j) := by linarith
    exact lt_of_mul_lt_mul_right this hK.le
  have hAE : 0 ≤ A*E1 := by
    have h' := mul_nonneg hA' (neg_nonneg.mpr hs1); rw [neg_mul_neg] at h'; exact h'
  have hBE : 0 ≤ B*E2 := mul_nonneg hB' hs2
  have hpowb : (1:ℝ) ≤ 2^(cL+b*m) := one_le_pow₀ (by norm_num)
  have key : (1:ℝ)/2 ≤ |(Q m:ℝ)| * |Λ| * 2^(cL+b*m) := by
    rw [← abs_mul]
    by_cases hN0 : N = 0
    · have ee : (Q m : ℝ) * Λ = A*E1 + B*E2 := by rw [hid, hN0]; simp
      have hge : -E1 ≤ (Q m:ℝ) * Λ := by
        have h' := mul_nonneg (show (0:ℝ) ≤ -(A+1) by rw [hA]; linarith) (neg_nonneg.mpr hs1)
        rw [ee]; linarith
      calc (1:ℝ)/2 ≤ 1 := by norm_num
        _ ≤ -E1 * 2^(cL+b*m) := hlow
        _ ≤ |(Q m:ℝ) * Λ| * 2^(cL+b*m) :=
          mul_le_mul_of_nonneg_right (le_trans hge (le_abs_self _)) (by positivity)
    · have hN1 : (1:ℝ) ≤ |(N:ℝ)| := by
        have := Int.one_le_abs hN0
        rw [← Int.cast_abs]; exact_mod_cast this
      have : (1:ℝ)/2 ≤ |(Q m : ℝ) * Λ| := by
        rw [hid]
        rcases le_or_gt 0 (N:ℝ) with hNp | hNn
        · rw [abs_of_nonneg hNp] at hN1
          calc (1:ℝ)/2 ≤ N + A*E1 + B*E2 := by linarith
            _ ≤ _ := le_abs_self _
        · rw [abs_of_neg hNn] at hN1
          calc (1:ℝ)/2 ≤ -(N + A*E1 + B*E2) := by linarith
            _ ≤ _ := neg_le_abs _
      calc (1:ℝ)/2 ≤ |(Q m : ℝ) * Λ| := this
        _ = |(Q m : ℝ) * Λ| * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hpowb (abs_nonneg _)
  have hpowY : (2:ℝ)^((a+b)*m) ≤ ((2:ℝ)^(cE+1+e) * (p+q))^r := by
    have hexp : (a+b)*m ≤ (e*j)*r := by
      rw [hm, show (a+b)*(d*j) = ((a+b)*d)*j by ring, show e*j*r = (e*r)*j by ring]
      exact Nat.mul_le_mul_right _ hr
    calc (2:ℝ)^((a+b)*m) ≤ 2^((e*j)*r) := pow_le_pow_right₀ (by norm_num) hexp
      _ = ((2:ℝ)^(e*j))^r := pow_mul _ _ _
      _ ≤ _ := by
        apply pow_le_pow_left₀ (by positivity)
        have : ((2^k0 : ℕ):ℝ) ≤ ((2^(cE+1) * (p+q) : ℕ) : ℝ) := by exact_mod_cast hXge
        push_cast at this
        calc (2:ℝ)^(e*j) ≤ 2^(k0+e) := pow_le_pow_right₀ (by norm_num) hj2
          _ = 2^k0 * 2^e := pow_add _ _ _
          _ ≤ (2^(cE+1) * (p+q)) * 2^e :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = (2:ℝ)^(cE+1+e) * (p+q) := by rw [pow_add]; ring
  have step : (1:ℝ)/2 ≤ 2^(cQ+cL) * 2^((a+b)*m) * |Λ| := by
    calc (1:ℝ)/2 ≤ |(Q m:ℝ)| * |Λ| * 2^(cL+b*m) := key
      _ ≤ 2^(cQ+a*m) * |Λ| * 2^(cL+b*m) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hQ hΛ0
      _ = 2^(cQ+cL) * 2^((a+b)*m) * |Λ| := by
        rw [pow_add, pow_add, pow_add, add_mul, pow_add]; ring
  have h2c5 : (2:ℝ) * 2^(cQ+cL) ≤ 2^(cQ+cL+5) := by
    calc (2:ℝ) * 2^(cQ+cL) ≤ 2^5 * 2^(cQ+cL) := by gcongr; norm_num
      _ = 2^(cQ+cL+5) := by ring
  calc (1:ℝ) ≤ 2 * 2^(cQ+cL) * 2^((a+b)*m) * |Λ| := by linarith
    _ ≤ 2 * 2^(cQ+cL) * ((2:ℝ)^(cE+1+e) * (p+q))^r * |Λ| := by
      apply mul_le_mul_of_nonneg_right _ hΛ0
      exact mul_le_mul_of_nonneg_left hpowY (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hΛ0
      exact mul_le_mul_of_nonneg_right h2c5 (by positivity)

/-- `SignApproxR` gives an explicit irrationality measure (unconditional implication):
if `d, e, t ≥ 1`, `(a+b)d ≤ e r`, `Q0 ≥ 3` and `2^{cQ+cL+5+(cE+3+e)r} ≤ Q0^t`, then
`|log₂3 − p/q| ≥ q^{−(r+1+t)}` for all `q ≥ Q0`, i.e. `IrrMeasHyp (r+1+t) Q0`. -/
theorem irrMeasHyp_of_signApproxR {a b cQ cE cL e d r t Q0 : ℕ} {Q P1 P2 : ℕ → ℤ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (hr : (a+b)*d ≤ e*r)
    (h : SignApproxR a b cQ cE cL e d Q P1 P2) (ht : 1 ≤ t) (hQ0 : 3 ≤ Q0)
    (hM : 2^(cQ+cL+5+(cE+3+e)*r) ≤ Q0^t) : IrrMeasHyp (r+1+t) Q0 := by
  intro p q hQq hq0
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l2lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hqr : (3:ℝ) ≤ q := by exact_mod_cast le_trans hQ0 hQq
  have hqpos : (0:ℝ) < q := by linarith
  have hqμ : (q:ℝ) ≤ (q:ℝ)^(r+1+t) := by
    calc (q:ℝ) = q^1 := (pow_one _).symm
      _ ≤ q^(r+1+t) := pow_le_pow_right₀ (by linarith) (by omega)
  have hqμpos : (0:ℝ) < (q:ℝ)^(r+1+t) := by positivity
  rcases le_or_gt (2*q) p with hp | hp
  · have h58 : Real.log 3 / Real.log 2 < 8/5 := by
      rw [div_lt_iff₀ l2]
      have : Real.log ((3:ℝ)^5) < Real.log ((2:ℝ)^8) :=
        Real.log_lt_log (by norm_num) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
    have hpq : (2:ℝ) ≤ p / q := by
      rw [le_div_iff₀ hqpos]; exact_mod_cast (by omega : 2*q ≤ p)
    have h1 : 1 / (q:ℝ)^(r+1+t) ≤ 1/3 := by
      rw [div_le_div_iff₀ hqμpos (by norm_num)]; linarith
    calc 1 / (q:ℝ)^(r+1+t) ≤ 1/3 := h1
      _ ≤ p/q - Real.log 3 / Real.log 2 := by linarith
      _ ≤ |Real.log 3 / Real.log 2 - p/q| := by rw [abs_sub_comm]; exact le_abs_self _
  · have hL := linForm_lower_of_signApproxR hd he hr h p q (by omega)
    set Λ : ℝ := (q:ℝ) * Real.log 3 - p * Real.log 2 with hΛ
    have hΛ0 := abs_nonneg Λ
    have hpq : (2:ℝ)^(cE+1+e) * ((p:ℝ)+q) ≤ 2^(cE+3+e) * q := by
      have : (p:ℝ) + q ≤ 4 * q := by
        have : (p:ℝ) < 2*q := by exact_mod_cast hp
        linarith
      have ee : (2:ℝ)^(cE+3+e) = 2^(cE+1+e) * 4 := by
        rw [show cE+3+e = (cE+1+e)+2 by ring, pow_add]; norm_num
      rw [ee, mul_assoc]; exact mul_le_mul_of_nonneg_left this (by positivity)
    set M : ℝ := (2:ℝ)^(cQ+cL+5+(cE+3+e)*r) with hMdef
    have hMq : M ≤ (q:ℝ)^t := by
      have : ((2^(cQ+cL+5+(cE+3+e)*r) : ℕ) : ℝ) ≤ ((Q0^t : ℕ) : ℝ) := by exact_mod_cast hM
      push_cast at this
      refine le_trans this (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQq) t)
    have hL2 : 1 ≤ M * (q:ℝ)^r * |Λ| := by
      have ee : M = 2^(cQ+cL+5) * ((2:ℝ)^(cE+3+e))^r := by
        rw [hMdef, ← pow_mul, ← pow_add]
      rw [ee, mul_assoc (2^(cQ+cL+5)), ← mul_pow]
      refine le_trans hL ?_
      apply mul_le_mul_of_nonneg_right _ hΛ0
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hpq _
    have hdiff : Real.log 3 / Real.log 2 - p/q = Λ / (q * Real.log 2) := by
      rw [hΛ]; field_simp
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * Real.log 2)]
    have hstep : |Λ| / q ≤ |Λ| / (q * Real.log 2) := by
      apply div_le_div_of_nonneg_left hΛ0 (by positivity)
      nlinarith
    refine le_trans ?_ hstep
    rw [div_le_div_iff₀ hqμpos hqpos, one_mul]
    have ee : (q:ℝ)^(r+1+t) = (q:ℝ)^r * q * q^t := by
      rw [pow_add, pow_add, pow_one]
    rw [ee]
    have hqad : (0:ℝ) < (q:ℝ)^r := by positivity
    have : M * (q:ℝ)^r * |Λ| * q ≤ |Λ| * ((q:ℝ)^r * q * q^t) := by
      have := mul_le_mul_of_nonneg_left hMq
        (by positivity : (0:ℝ) ≤ (q:ℝ)^r * |Λ| * q)
      nlinarith
    nlinarith

end Collatz

#print axioms Collatz.signApproxR_of_signApprox
#print axioms Collatz.linForm_lower_of_signApproxR
#print axioms Collatz.irrMeasHyp_of_signApproxR
