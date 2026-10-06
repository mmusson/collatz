import FareyBigCond

/-!
# Type-II transference, simultaneous approximations → `IrrMeasHyp`

`SimApprox a c d Q x y`: integer sequences with `|Q_n| ≤ 2^{c+an}`,
`|Q_n log 2 − x_n|·2^{⌊n/d⌋} ≤ 2^c`, `|Q_n log 3 − y_n|·2^{⌊n/d⌋} ≤ 2^c` and
`Δ_n = x_n y_{n+1} − x_{n+1} y_n ≠ 0` for all `n`.  This is a DEFINITION (hypothesis
interface), not an axiom; it is meant to be discharged by the 4-root family of
`PadeArith.lean` (T1) plus a sup bound, the integral/finite-sum identity and `Δ_n ≠ 0`
for all `n`, none of which are formalized (Δ_n ≠ 0 is checked numerically only, n ≤ 29).
Unlike type-I `SchemeHyp` (needs decay exponent > coefficient exponent, impossible for
Hata-type families with a ≈ 37 bits and decay < 1 bit per index), this interface allows
arbitrary `a`.
* `linForm_lower_of_simApprox`: `1 ≤ 2^{c+1+a} (2^{c+2}(p+q))^{ad} |q log 3 − p log 2|`.
* `irrMeasHyp_of_simApprox`: if `2^{c+1+a+(c+4)ad} ≤ Q0^t`, `t ≥ 1`, `Q0 ≥ 3`, then
  `IrrMeasHyp (ad+1+t) Q0`.
* `few_runs_cycle_trivial_of_simApprox`: CONDITIONAL on `SimApprox`, with `Q0 ≤ K1big` and
  `8(30+17(ad+t)+2) ≤ 2^16`: every positive `T`-cycle with `≤ 2` odd runs is trivial
  (classical Steiner 1977 / Simons 2005 statement).
-/

namespace Collatz

/-- Type-II simultaneous approximation data for `(log 2, log 3)` (hypothesis interface). -/
def SimApprox (a c d : ℕ) (Q x y : ℕ → ℤ) : Prop := ∀ n : ℕ,
  |(Q n : ℝ)| ≤ 2^(c + a*n) ∧
  |(Q n : ℝ) * Real.log 2 - x n| * 2^(n/d) ≤ 2^c ∧
  |(Q n : ℝ) * Real.log 3 - y n| * 2^(n/d) ≤ 2^c ∧
  x n * y (n+1) - x (n+1) * y n ≠ 0

/-- Lower bound for `|q log 3 − p log 2|` from `SimApprox` (unconditional implication). -/
theorem linForm_lower_of_simApprox {a c d : ℕ} {Q x y : ℕ → ℤ} (hd : 1 ≤ d)
    (h : SimApprox a c d Q x y) (p q : ℕ) (hq : 1 ≤ q) :
    1 ≤ (2:ℝ)^(c+1+a) * ((2:ℝ)^(c+2) * (p+q))^(a*d) *
      |(q:ℝ) * Real.log 3 - p * Real.log 2| := by
  set Λ : ℝ := (q:ℝ) * Real.log 3 - p * Real.log 2 with hΛ
  set X : ℕ := 2^(c+1) * (p+q) with hXdef
  have hX0 : X ≠ 0 := by positivity
  set k := Nat.log 2 X with hk
  have hXlt : X < 2^(k+1) := Nat.lt_pow_succ_log_self (by norm_num) X
  have hXge : 2^k ≤ X := Nat.pow_log_le_self 2 hX0
  set n := d * (k+1) with hn
  have hnd : n / d = k+1 := Nat.mul_div_cancel_left (k+1) (by omega)
  -- the small-error bound at m ∈ {n, n+1}
  have hsmall : ∀ m, n ≤ m →
      |(q:ℝ) * ((Q m : ℝ) * Real.log 3 - y m) - p * ((Q m : ℝ) * Real.log 2 - x m)| < 1/2 := by
    intro m hm
    have hmd : k+1 ≤ m / d := hnd ▸ Nat.div_le_div_right hm
    obtain ⟨_, h2, h3, _⟩ := h m
    set ξ := (Q m : ℝ) * Real.log 2 - x m
    set η := (Q m : ℝ) * Real.log 3 - y m
    have hpow : (2:ℝ)^(k+1) ≤ 2^(m/d) := pow_le_pow_right₀ (by norm_num) hmd
    have hξ : |ξ| * 2^(k+1) ≤ 2^c :=
      le_trans (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) h2
    have hη : |η| * 2^(k+1) ≤ 2^c :=
      le_trans (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) h3
    have hXr : (2:ℝ)^(c+1) * ((p:ℝ)+q) < 2^(k+1) := by
      have : ((2^(c+1) * (p+q) : ℕ) : ℝ) < ((2^(k+1) : ℕ) : ℝ) := by exact_mod_cast hXlt
      push_cast at this; exact this
    have hK : (0:ℝ) < 2^(k+1) := by positivity
    have htri : |(q:ℝ) * η - p * ξ| ≤ q * |η| + p * |ξ| := by
      calc |(q:ℝ) * η - p * ξ| ≤ |(q:ℝ) * η| + |(p:ℝ) * ξ| := abs_sub _ _
        _ = q * |η| + p * |ξ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ q),
            abs_of_nonneg (by positivity : (0:ℝ) ≤ p)]
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq
    have hsum : ((q:ℝ) * |η| + p * |ξ|) * 2^(k+1) ≤ ((p:ℝ) + q) * 2^c := by
      nlinarith [abs_nonneg η, abs_nonneg ξ, (Nat.cast_nonneg p : (0:ℝ) ≤ p)]
    have h2c : (2:ℝ)^(c+1) = 2 * 2^c := by ring
    rw [h2c] at hXr
    have : ((q:ℝ) * |η| + p * |ξ|) * 2^(k+1) < (1/2) * 2^(k+1) := by
      nlinarith
    have := lt_of_mul_lt_mul_right this hK.le
    linarith
  -- non-vanishing
  have hz : ∃ m, n ≤ m ∧ m ≤ n+1 ∧ (q:ℤ) * y m - p * x m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hcon n le_rfl (by omega)
    have h1 := hcon (n+1) (by omega) le_rfl
    have hΔ := (h n).2.2.2
    have hqz : (q:ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    apply hΔ
    have : (q:ℤ) * (x n * y (n+1) - x (n+1) * y n) = 0 := by
      linear_combination (x n) * h1 - (x (n+1)) * h0
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hqz
    · exact h'
  obtain ⟨m, hnm, hmn, hzm⟩ := hz
  have hz1 : (1:ℝ) ≤ |((((q:ℤ) * y m - p * x m : ℤ)) : ℝ)| := by
    have := Int.one_le_abs hzm
    rw [← Int.cast_abs]; exact_mod_cast this
  have hid : (((q:ℤ) * y m - p * x m : ℤ) : ℝ) = (Q m : ℝ) * Λ -
      ((q:ℝ) * ((Q m : ℝ) * Real.log 3 - y m) - p * ((Q m : ℝ) * Real.log 2 - x m)) := by
    push_cast; ring
  rw [hid] at hz1
  have hs := hsmall m hnm
  have hQΛ : (1:ℝ)/2 < |(Q m : ℝ)| * |Λ| := by
    have := abs_sub (Q m * Λ) ((q:ℝ) * ((Q m : ℝ) * Real.log 3 - y m) - p * ((Q m : ℝ) * Real.log 2 - x m))
    rw [abs_mul] at this
    linarith
  have hQ : |(Q m : ℝ)| ≤ 2^(c + a*(n+1)) :=
    le_trans (h m).1 (pow_le_pow_right₀ (by norm_num) (by nlinarith))
  have hpow2 : (2:ℝ)^(a*(n+1)) ≤ 2^a * ((2:ℝ)^(c+2) * (p+q))^(a*d) := by
    have e : a*(n+1) = a + (k+1)*(a*d) := by rw [hn]; ring
    rw [e, pow_add, pow_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have : ((2^k : ℕ):ℝ) ≤ ((2^(c+1) * (p+q) : ℕ) : ℝ) := by exact_mod_cast hXge
    push_cast at this
    have e2 : (2:ℝ)^(c+2) * ((p:ℝ)+q) = 2 * (2^(c+1) * ((p:ℝ)+q)) := by ring
    rw [e2, pow_succ]; linarith
  have hΛ0 := abs_nonneg Λ
  have key : (1:ℝ)/2 < 2^c * (2^a * ((2:ℝ)^(c+2) * (p+q))^(a*d)) * |Λ| := by
    calc (1:ℝ)/2 < |(Q m : ℝ)| * |Λ| := hQΛ
      _ ≤ 2^(c + a*(n+1)) * |Λ| := mul_le_mul_of_nonneg_right hQ hΛ0
      _ = 2^c * 2^(a*(n+1)) * |Λ| := by rw [pow_add]
      _ ≤ 2^c * (2^a * ((2:ℝ)^(c+2) * (p+q))^(a*d)) * |Λ| := by
        apply mul_le_mul_of_nonneg_right _ hΛ0
        exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
  have e3 : (2:ℝ)^(c+1+a) = 2 * (2^c * 2^a) := by ring
  rw [e3]
  nlinarith


/-- `SimApprox` gives the irrationality measure `IrrMeasHyp (ad+1+t) Q0` (unconditional implication). -/
theorem irrMeasHyp_of_simApprox {a c d t Q0 : ℕ} {Q x y : ℕ → ℤ} (hd : 1 ≤ d)
    (h : SimApprox a c d Q x y) (ht : 1 ≤ t) (hQ0 : 3 ≤ Q0)
    (hM : 2^(c+1+a+(c+4)*a*d) ≤ Q0^t) : IrrMeasHyp (a*d+1+t) Q0 := by
  intro p q hQq hq0
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l2lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hqr : (3:ℝ) ≤ q := by exact_mod_cast le_trans hQ0 hQq
  have hqpos : (0:ℝ) < q := by linarith
  have hqμ : (q:ℝ) ≤ (q:ℝ)^(a*d+1+t) := by
    calc (q:ℝ) = q^1 := (pow_one _).symm
      _ ≤ q^(a*d+1+t) := pow_le_pow_right₀ (by linarith) (by omega)
  have hqμpos : (0:ℝ) < (q:ℝ)^(a*d+1+t) := by positivity
  rcases le_or_gt (2*q) p with hp | hp
  · -- p/q ≥ 2 > 8/5 > log 3/log 2
    have h58 : Real.log 3 / Real.log 2 < 8/5 := by
      rw [div_lt_iff₀ l2]
      have : Real.log ((3:ℝ)^5) < Real.log ((2:ℝ)^8) :=
        Real.log_lt_log (by norm_num) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
    have hpq : (2:ℝ) ≤ p / q := by
      rw [le_div_iff₀ hqpos]; exact_mod_cast (by omega : 2*q ≤ p)
    have h1 : 1 / (q:ℝ)^(a*d+1+t) ≤ 1/3 := by
      rw [div_le_div_iff₀ hqμpos (by norm_num)]; linarith
    calc 1 / (q:ℝ)^(a*d+1+t) ≤ 1/3 := h1
      _ ≤ p/q - Real.log 3 / Real.log 2 := by linarith
      _ ≤ |Real.log 3 / Real.log 2 - p/q| := by rw [abs_sub_comm]; exact le_abs_self _
  · have hL := linForm_lower_of_simApprox hd h p q (by omega)
    set Λ : ℝ := (q:ℝ) * Real.log 3 - p * Real.log 2 with hΛ
    have hΛ0 := abs_nonneg Λ
    have hpq : (2:ℝ)^(c+2) * ((p:ℝ)+q) ≤ 2^(c+4) * q := by
      have : (p:ℝ) + q ≤ 4 * q := by
        have : (p:ℝ) < 2*q := by exact_mod_cast hp
        linarith
      have e : (2:ℝ)^(c+4) = 2^(c+2) * 4 := by ring
      rw [e, mul_assoc]; exact mul_le_mul_of_nonneg_left this (by positivity)
    set M : ℝ := (2:ℝ)^(c+1+a+(c+4)*a*d) with hMdef
    have hMq : M ≤ (q:ℝ)^t := by
      have : ((2^(c+1+a+(c+4)*a*d) : ℕ) : ℝ) ≤ ((Q0^t : ℕ) : ℝ) := by exact_mod_cast hM
      push_cast at this
      refine le_trans this (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQq) t)
    have hL2 : 1 ≤ M * (q:ℝ)^(a*d) * |Λ| := by
      have e : M = 2^(c+1+a) * ((2:ℝ)^(c+4))^(a*d) := by
        rw [hMdef, ← pow_mul, ← pow_add]; congr 1; ring
      rw [e, mul_assoc (2^(c+1+a)), ← mul_pow]
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
    have e : (q:ℝ)^(a*d+1+t) = (q:ℝ)^(a*d) * q * q^t := by rw [pow_add, pow_add, pow_one]
    rw [e]
    have hqad : (0:ℝ) < (q:ℝ)^(a*d) := by positivity
    have : M * (q:ℝ)^(a*d) * |Λ| * q ≤ |Λ| * ((q:ℝ)^(a*d) * q * q^t) := by
      have := mul_le_mul_of_nonneg_left hMq (by positivity : (0:ℝ) ≤ (q:ℝ)^(a*d) * |Λ| * q)
      nlinarith
    nlinarith

/-- **CONDITIONAL on `SimApprox`**: `≤ 2`-run `T`-cycles are trivial. -/
theorem few_runs_cycle_trivial_of_simApprox {a c d t Q0 : ℕ} {Q x y : ℕ → ℤ} (hd : 1 ≤ d)
    (h : SimApprox a c d Q x y) (ht : 1 ≤ t) (hQ0 : 3 ≤ Q0) (hQK : Q0 ≤ K1big)
    (hM : 2^(c+1+a+(c+4)*a*d) ≤ Q0^t) (hside : 8 * (30 + 17 * (a*d+t) + 2) ≤ 2^16)
    {z L : ℕ} (hz : 0 < z) (hL : 0 < L) (hc : CollatzProof.T^[L] z = z) (hr : oddRuns L z ≤ 2) :
    z = 1 ∨ z = 2 := by
  have hμ : a*d+1+t - 1 = a*d+t := by omega
  exact few_runs_cycle_trivial_of_irrMeas_big (by omega) (by omega) hQK (by rw [hμ]; exact hside)
    (irrMeasHyp_of_simApprox hd h ht hQ0 hM) hz hL hc hr

end Collatz

#print axioms Collatz.linForm_lower_of_simApprox
#print axioms Collatz.irrMeasHyp_of_simApprox
#print axioms Collatz.few_runs_cycle_trivial_of_simApprox
