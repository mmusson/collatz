import TypeIITransfer

/-!
# Sign-split transference

Write `M1 = 2 log 2 − log 3 = log(4/3)` and `M2 = 2 log 3 − 3 log 2 = log(9/8)`. Then
`q log 3 − p log 2 = (3q−2p) M1 + (2q−p) M2`, and in the only nontrivial range
`3q < 2p < 4q` the coefficient `A = 3q−2p` is `≤ −1` and `B = 2q−p` is `≥ 1`.
`SignApprox a b c d Q P1 P2` (a DEFINITION, i.e. a hypothesis interface, NOT an axiom; since
`PadeSup`/`FewRunsUncond` it HAS an unconditional witness, `signApprox_Vq` in `FewRunsUncond.lean`) asks for integer forms `E1 = Q M1 − P1 ≤ 0 ≤ E2 = Q M2 − P2`
with the usual size and decay bounds and a LOWER bound `|E1| ≥ 2^{−(c+bm)}`. If the
integer `N = A P1 + B P2` is `0`, then `QΛ = A E1 + B E2 ≥ |E1| > 0` because both terms are
`≥ 0`. So no determinant/`Δ_n ≠ 0`/window non-vanishing is needed: this replaces
`SimApprox`/`SimApproxW` (`PadeArith`/`TypeIITransfer`/`TypeIIWindow`/`PadeBounds`).
* `linForm_lower_of_signApprox`: `1 ≤ 2^{2c+5}(2^{c+5}(p+q))^{(a+b)d}|q log 3 − p log 2|`.
* `irrMeasHyp_of_signApprox`: `2^{2c+5+(c+7)(a+b)d} ≤ Q0^t`, `t ≥ 1`, `Q0 ≥ 3` ⇒
  `IrrMeasHyp ((a+b)d+1+t) Q0`.
* `few_runs_cycle_trivial_of_signApprox`: implication from `SignApprox`: positive `T`-cycles
  with `≤ 2` odd runs are trivial (the classical Steiner 1977 / Simons 2005 statement).
(`RunsTail` update) The witness is the family `Vq_n` of `PadeArithQ.lean` (odd `n`):
`signApprox_Vq : SignApprox 74 37 46 2 ...` (`FewRunsUncond.lean`, `PadeSup`/`FewRunsUncond`) proves all conjuncts,
so the results here are used unconditionally in `few_runs_cycle_trivial_uncond` (`PadeSup`/`FewRunsUncond`) and
`linFormHyp_uncond` (`RunsTail.lean`, `RunsTail`).
-/

namespace Collatz

/-- Sign-split approximation data for `(log(4/3), log(9/8))` (hypothesis interface; witness
`signApprox_Vq` in `FewRunsUncond.lean`, `PadeSup`/`FewRunsUncond`): for every index `m`, `|Q_m| ≤ 2^{c+am}`; `|E_j(m)|·2^{⌊m/d⌋} ≤ 2^c` for
`E1 = Q_m log(4/3) − P1_m`, `E2 = Q_m log(9/8) − P2_m`; `E1 ≤ 0 ≤ E2`; `1 ≤ |E1|·2^{c+bm}`. -/
def SignApprox (a b c d : ℕ) (Q P1 P2 : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, |(Q m : ℝ)| ≤ 2^(c + a*m) ∧
    |(Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m| * 2^(m/d) ≤ 2^c ∧
    |(Q m : ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2 m| * 2^(m/d) ≤ 2^c ∧
    (Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m ≤ 0 ∧
    0 ≤ (Q m : ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2 m ∧
    1 ≤ |(Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m| * 2^(c + b*m)

/-- `log(4/3) ≥ 1/4`. -/
theorem log_four_thirds_ge : (1:ℝ)/4 ≤ 2*Real.log 2 - Real.log 3 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 4/3 by norm_num)
  have e : Real.log (4/3 : ℝ) = 2*Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h; norm_num at h; linarith

/-- `log(9/8) ≥ 1/9`. -/
theorem log_nine_eighths_ge : (1:ℝ)/9 ≤ 2*Real.log 3 - 3*Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 9/8 by norm_num)
  have e : Real.log (9/8 : ℝ) = 2*Real.log 3 - 3*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (9:ℝ) = 3^2 by norm_num,
      show (8:ℝ) = 2^3 by norm_num, Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [e] at h; norm_num at h; linarith

/-- Lower bound for `|q log 3 − p log 2|` from `SignApprox` (unconditional implication;
instantiated unconditionally via `signApprox_Vq`, `FewRunsUncond.lean`):
`1 ≤ 2^{2c+5}(2^{c+5}(p+q))^{(a+b)d}|q log 3 − p log 2|` for `q ≥ 1`, `d ≥ 1`. -/
theorem linForm_lower_of_signApprox {a b c d : ℕ} {Q P1 P2 : ℕ → ℤ} (hd : 1 ≤ d)
    (h : SignApprox a b c d Q P1 P2) (p q : ℕ) (hq : 1 ≤ q) :
    1 ≤ (2:ℝ)^(2*c+5) * ((2:ℝ)^(c+5) * (p+q))^((a+b)*d) *
      |(q:ℝ) * Real.log 3 - p * Real.log 2| := by
  set Λ : ℝ := (q:ℝ) * Real.log 3 - p * Real.log 2 with hΛ
  have hM1 := log_four_thirds_ge
  have hM2 := log_nine_eighths_ge
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have hY1 : (1:ℝ) ≤ (2:ℝ)^(c+5) * (p+q) := by
    have : (1:ℝ) ≤ 2^(c+5) := one_le_pow₀ (by norm_num)
    nlinarith
  have hYe : (1:ℝ) ≤ ((2:ℝ)^(c+5) * (p+q))^((a+b)*d) := one_le_pow₀ hY1
  have h2c : (32:ℝ) ≤ 2^(2*c+5) := by
    calc (32:ℝ) = 2^5 := by norm_num
      _ ≤ 2^(2*c+5) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hΛ0 := abs_nonneg Λ
  have easy : (1:ℝ)/18 ≤ |Λ| →
      1 ≤ 2^(2*c+5) * ((2:ℝ)^(c+5) * (p+q))^((a+b)*d) * |Λ| := by
    intro hl
    have : (32:ℝ) * 1 * (1/18) ≤ 2^(2*c+5) * ((2:ℝ)^(c+5) * (p+q))^((a+b)*d) * |Λ| :=
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
  set X : ℕ := 2^(c+4) * (p+q) with hXdef
  have hX0 : X ≠ 0 := by positivity
  set k0 := Nat.log 2 X with hk
  have hXlt : X < 2^(k0+1) := Nat.lt_pow_succ_log_self (by norm_num) X
  have hXge : 2^k0 ≤ X := Nat.pow_log_le_self 2 hX0
  set m := d * (k0+1) with hm
  have hmd : m / d = k0+1 := Nat.mul_div_cancel_left (k0+1) (by omega)
  obtain ⟨hQ, hE1, hE2, hs1, hs2, hlow⟩ := h m
  rw [hmd] at hE1 hE2
  set E1 := (Q m : ℝ) * (2*Real.log 2 - Real.log 3) - P1 m with hE1def
  set E2 := (Q m : ℝ) * (2*Real.log 3 - 3*Real.log 2) - P2 m with hE2def
  set A : ℝ := 3*q - 2*p with hA
  set B : ℝ := 2*q - p with hB
  set N : ℤ := (3*q - 2*p : ℤ) * P1 m + (2*q - p : ℤ) * P2 m with hN
  have hid : (Q m : ℝ) * Λ = N + A*E1 + B*E2 := by
    rw [hN, hA, hB, hE1def, hE2def, hΛ]; push_cast; ring
  have hK : (0:ℝ) < 2^(k0+1) := by positivity
  have hXr : (2:ℝ)^(c+4) * (p+q) < 2^(k0+1) := by
    have : ((2^(c+4) * (p+q) : ℕ) : ℝ) < ((2^(k0+1) : ℕ) : ℝ) := by exact_mod_cast hXlt
    push_cast at this; exact this
  have habs1 : |E1| = -E1 := abs_of_nonpos hs1
  have habs2 : |E2| = E2 := abs_of_nonneg hs2
  rw [habs1] at hE1 hlow
  rw [habs2] at hE2
  have hA' : 0 ≤ -A := by rw [hA]; linarith
  have hB' : 0 ≤ B := by rw [hB]; linarith
  have hS : (A*E1 + B*E2) * 2^(k0+1) ≤ (p+q) * 2^c := by
    have e : (A*E1 + B*E2) * 2^(k0+1) = (-A) * ((-E1) * 2^(k0+1)) + B * (E2 * 2^(k0+1)) := by
      ring
    rw [e]
    have h2c0 : (0:ℝ) < 2^c := by positivity
    calc _ ≤ (-A) * 2^c + B * 2^c :=
          add_le_add (mul_le_mul_of_nonneg_left hE1 hA') (mul_le_mul_of_nonneg_left hE2 hB')
      _ = (p - q) * 2^c := by rw [hA, hB]; ring
      _ ≤ (p+q) * 2^c := mul_le_mul_of_nonneg_right (by linarith) h2c0.le
  have hS16 : A*E1 + B*E2 < 1/16 := by
    have e : (2:ℝ)^(c+4) = 16 * 2^c := by ring
    rw [e] at hXr
    have : (A*E1 + B*E2) * 2^(k0+1) < (1/16) * 2^(k0+1) := by linarith
    exact lt_of_mul_lt_mul_right this hK.le
  have hAE : 0 ≤ A*E1 := by
    have h' := mul_nonneg hA' (neg_nonneg.mpr hs1); rw [neg_mul_neg] at h'; exact h'
  have hBE : 0 ≤ B*E2 := mul_nonneg hB' hs2
  have hpowb : (1:ℝ) ≤ 2^(c+b*m) := one_le_pow₀ (by norm_num)
  have key : (1:ℝ)/2 ≤ |(Q m:ℝ)| * |Λ| * 2^(c+b*m) := by
    rw [← abs_mul]
    by_cases hN0 : N = 0
    · have e : (Q m : ℝ) * Λ = A*E1 + B*E2 := by rw [hid, hN0]; simp
      have hge : -E1 ≤ (Q m:ℝ) * Λ := by
        have h' := mul_nonneg (show (0:ℝ) ≤ -(A+1) by rw [hA]; linarith) (neg_nonneg.mpr hs1)
        rw [e]; linarith
      calc (1:ℝ)/2 ≤ 1 := by norm_num
        _ ≤ -E1 * 2^(c+b*m) := hlow
        _ ≤ |(Q m:ℝ) * Λ| * 2^(c+b*m) :=
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
  have hpowY : (2:ℝ)^((a+b)*m) ≤ ((2:ℝ)^(c+5) * (p+q))^((a+b)*d) := by
    have e : (a+b)*m = (k0+1)*((a+b)*d) := by rw [hm]; ring
    rw [e, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    have : ((2^k0 : ℕ):ℝ) ≤ ((2^(c+4) * (p+q) : ℕ) : ℝ) := by exact_mod_cast hXge
    push_cast at this
    have e1 : (2:ℝ)^(k0+1) = 2^k0 * 2 := pow_succ _ _
    have e2 : (2:ℝ)^(c+5) = 2^(c+4) * 2 := pow_succ _ _
    rw [e1, e2]; linarith
  have step : (1:ℝ)/2 ≤ 2^(2*c) * 2^((a+b)*m) * |Λ| := by
    calc (1:ℝ)/2 ≤ |(Q m:ℝ)| * |Λ| * 2^(c+b*m) := key
      _ ≤ 2^(c+a*m) * |Λ| * 2^(c+b*m) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hQ hΛ0
      _ = 2^(2*c) * 2^((a+b)*m) * |Λ| := by ring
  have h2c5 : (2:ℝ) * 2^(2*c) ≤ 2^(2*c+5) := by
    calc (2:ℝ) * 2^(2*c) ≤ 2^5 * 2^(2*c) := by gcongr; norm_num
      _ = 2^(2*c+5) := by ring
  calc (1:ℝ) ≤ 2 * 2^(2*c) * 2^((a+b)*m) * |Λ| := by linarith
    _ ≤ 2 * 2^(2*c) * ((2:ℝ)^(c+5) * (p+q))^((a+b)*d) * |Λ| := by
      apply mul_le_mul_of_nonneg_right _ hΛ0
      exact mul_le_mul_of_nonneg_left hpowY (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hΛ0
      exact mul_le_mul_of_nonneg_right h2c5 (by positivity)

/-- `SignApprox` gives `IrrMeasHyp ((a+b)d+1+t) Q0` (unconditional implication; with the
witness `signApprox_Vq` it yields the unconditional `IrrMeasHyp 342 (2^100)`, used in
`linFormHyp_uncond`, `RunsTail.lean`, `RunsTail`). -/
theorem irrMeasHyp_of_signApprox {a b c d t Q0 : ℕ} {Q P1 P2 : ℕ → ℤ} (hd : 1 ≤ d)
    (h : SignApprox a b c d Q P1 P2) (ht : 1 ≤ t) (hQ0 : 3 ≤ Q0)
    (hM : 2^(2*c+5+(c+7)*((a+b)*d)) ≤ Q0^t) : IrrMeasHyp ((a+b)*d+1+t) Q0 := by
  intro p q hQq hq0
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l2lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hqr : (3:ℝ) ≤ q := by exact_mod_cast le_trans hQ0 hQq
  have hqpos : (0:ℝ) < q := by linarith
  have hqμ : (q:ℝ) ≤ (q:ℝ)^((a+b)*d+1+t) := by
    calc (q:ℝ) = q^1 := (pow_one _).symm
      _ ≤ q^((a+b)*d+1+t) := pow_le_pow_right₀ (by linarith) (by omega)
  have hqμpos : (0:ℝ) < (q:ℝ)^((a+b)*d+1+t) := by positivity
  rcases le_or_gt (2*q) p with hp | hp
  · have h58 : Real.log 3 / Real.log 2 < 8/5 := by
      rw [div_lt_iff₀ l2]
      have : Real.log ((3:ℝ)^5) < Real.log ((2:ℝ)^8) :=
        Real.log_lt_log (by norm_num) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
    have hpq : (2:ℝ) ≤ p / q := by
      rw [le_div_iff₀ hqpos]; exact_mod_cast (by omega : 2*q ≤ p)
    have h1 : 1 / (q:ℝ)^((a+b)*d+1+t) ≤ 1/3 := by
      rw [div_le_div_iff₀ hqμpos (by norm_num)]; linarith
    calc 1 / (q:ℝ)^((a+b)*d+1+t) ≤ 1/3 := h1
      _ ≤ p/q - Real.log 3 / Real.log 2 := by linarith
      _ ≤ |Real.log 3 / Real.log 2 - p/q| := by rw [abs_sub_comm]; exact le_abs_self _
  · have hL := linForm_lower_of_signApprox hd h p q (by omega)
    set Λ : ℝ := (q:ℝ) * Real.log 3 - p * Real.log 2 with hΛ
    have hΛ0 := abs_nonneg Λ
    have hpq : (2:ℝ)^(c+5) * ((p:ℝ)+q) ≤ 2^(c+7) * q := by
      have : (p:ℝ) + q ≤ 4 * q := by
        have : (p:ℝ) < 2*q := by exact_mod_cast hp
        linarith
      have e : (2:ℝ)^(c+7) = 2^(c+5) * 4 := by ring
      rw [e, mul_assoc]; exact mul_le_mul_of_nonneg_left this (by positivity)
    set M : ℝ := (2:ℝ)^(2*c+5+(c+7)*((a+b)*d)) with hMdef
    have hMq : M ≤ (q:ℝ)^t := by
      have : ((2^(2*c+5+(c+7)*((a+b)*d)) : ℕ) : ℝ) ≤ ((Q0^t : ℕ) : ℝ) := by exact_mod_cast hM
      push_cast at this
      refine le_trans this (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQq) t)
    have hL2 : 1 ≤ M * (q:ℝ)^((a+b)*d) * |Λ| := by
      have e : M = 2^(2*c+5) * ((2:ℝ)^(c+7))^((a+b)*d) := by
        rw [hMdef, ← pow_mul, ← pow_add]
      rw [e, mul_assoc (2^(2*c+5)), ← mul_pow]
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
    have e : (q:ℝ)^((a+b)*d+1+t) = (q:ℝ)^((a+b)*d) * q * q^t := by
      rw [pow_add, pow_add, pow_one]
    rw [e]
    have hqad : (0:ℝ) < (q:ℝ)^((a+b)*d) := by positivity
    have : M * (q:ℝ)^((a+b)*d) * |Λ| * q ≤ |Λ| * ((q:ℝ)^((a+b)*d) * q * q^t) := by
      have := mul_le_mul_of_nonneg_left hMq
        (by positivity : (0:ℝ) ≤ (q:ℝ)^((a+b)*d) * |Λ| * q)
      nlinarith
    nlinarith

/-- **Implication from `SignApprox`** (witness `signApprox_Vq`, `FewRunsUncond.lean`; the
unconditional instance is `few_runs_cycle_trivial_uncond`): positive `T`-cycles with `≤ 2` odd
runs are trivial. -/
theorem few_runs_cycle_trivial_of_signApprox {a b c d t Q0 : ℕ} {Q P1 P2 : ℕ → ℤ}
    (hd : 1 ≤ d) (h : SignApprox a b c d Q P1 P2) (ht : 1 ≤ t) (hQ0 : 3 ≤ Q0)
    (hQK : Q0 ≤ K1big) (hM : 2^(2*c+5+(c+7)*((a+b)*d)) ≤ Q0^t)
    (hside : 8 * (30 + 17 * ((a+b)*d+t) + 2) ≤ 2^16)
    {z L : ℕ} (hz : 0 < z) (hL : 0 < L) (hc : CollatzProof.T^[L] z = z)
    (hr : oddRuns L z ≤ 2) : z = 1 ∨ z = 2 := by
  have hμ : (a+b)*d+1+t - 1 = (a+b)*d+t := by omega
  exact few_runs_cycle_trivial_of_irrMeas_big (by omega) (by omega) hQK
    (by rw [hμ]; exact hside) (irrMeasHyp_of_signApprox hd h ht hQ0 hM) hz hL hc hr

end Collatz

#print axioms Collatz.log_four_thirds_ge
#print axioms Collatz.log_nine_eighths_ge
#print axioms Collatz.linForm_lower_of_signApprox
#print axioms Collatz.irrMeasHyp_of_signApprox
#print axioms Collatz.few_runs_cycle_trivial_of_signApprox
